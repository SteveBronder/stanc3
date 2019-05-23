(** Generate C++ from the MIR.

    This module makes extensive use of the Format[0] module via the Fmt[1] API.
    As such, you'll need to understand the "%a" and "@" notation from [0], especially
    the section headed "Formatted pretty-printing." Then, we use functions like
    [pf] and [strf] from the Fmt library[1]. On top of that, the "@" pretty-printing
    specifiers all actually correspond 1-to-1 with commands like [open_box] from
    the Format library[0]. The boxing system is best described in this explainer
    pdf [2], particularly Section 3 ("Format basics"). It's worth noting that someone
    was able to make a decent-looking pretty-printer for a subset of Javascript[3] that
    might serve as a good reference. Good luck!

    [0] Format module doc: https://caml.inria.fr/pub/docs/manual-ocaml/libref/Format.html
    [1] Fmt module doc: https://erratique.ch/software/fmt/doc/Fmt.html
    [2] Format Unraveled: https://hal.archives-ouvertes.fr/hal-01503081/file/format-unraveled.pdf
    [3] Javascript pretty-printer https://github.com/Virum/compiler/blob/28e807b842bab5dcf11460c8193dd5b16674951f/JavaScript.ml#L112
*)

open Core_kernel
open Middle
open Fmt
open Expression_gen

let pp_call ppf (name, pp_arg, args) =
  pf ppf "%s(@[<hov>%a@])" name (list ~sep:comma pp_arg) args

let pp_call_str ppf (name, args) = pp_call ppf (name, string, args)
let pp_block ppf (pp_body, body) = pf ppf "{@;<1 2>@[<v>%a@]@,}" pp_body body

let pp_set_size ppf (decl_id, st, adtype) =
  (* TODO: generate optimal adtypes for expressions and declarations *)
  ignore adtype ;
  let rec pp_size_ctor ppf st =
    let pp_st ppf st =
      pf ppf "%a" pp_unsizedtype_local (adtype, remove_size st)
    in
    match st with
    | SInt | SReal -> pf ppf "0"
    | SVector d | SRowVector d -> pf ppf "%a(%a)" pp_st st pp_expr d
    | SMatrix (d1, d2) -> pf ppf "%a(%a, %a)" pp_st st pp_expr d1 pp_expr d2
    | SArray (t, d) -> pf ppf "%a(%a, %a)" pp_st st pp_expr d pp_size_ctor t
  in
  match st with
  | SInt | SReal -> ()
  | st -> pf ppf "%s = %a;@," decl_id pp_size_ctor st

let%expect_test "set size mat array" =
  let int i = {expr= Lit (Int, string_of_int i); emeta= internal_meta} in
  strf "@[<v>%a@]" pp_set_size
    ("d", SArray (SArray (SMatrix (int 2, int 3), int 4), int 5), DataOnly)
  |> print_endline ;
  [%expect
    {| d = std::vector<std::vector<Eigen::Matrix<double, -1, -1>>>(5, std::vector<Eigen::Matrix<double, -1, -1>>(4, Eigen::Matrix<double, -1, -1>(2, 3))); |}]

let pp_indexed_simple ppf (vident, idcs) =
  let minus_one e =
    { expr= FunApp (StanLib, string_of_operator Minus, [e; loop_bottom])
    ; emeta= e.emeta }
  in
  let idx_minus_one = map_index minus_one in
  (Pretty.pp_indexed pp_expr) ppf (vident, List.map ~f:idx_minus_one idcs)

(** [pp_for_loop ppf (loopvar, lower, upper, pp_body, body)] tries to
    pretty print a for-loop from lower to upper given some loopvar.*)
let pp_for_loop ppf (loopvar, lower, upper, pp_body, body) =
  pf ppf "@[<hov>for (@[<hov>size_t %s = %a;@ %s <= %a;@ ++%s@])" loopvar
    pp_expr lower loopvar pp_expr upper loopvar ;
  pf ppf " %a@]" pp_body body

let rec pp_for_loop_iteratee ?(index_ids = []) ppf (iteratee, st, pp_body) =
  let iter d pp_body =
    let loopvar, gensym_exit = gensym_enter () in
    pp_for_loop ppf
      ( loopvar
      , loop_bottom
      , d
      , pp_block
      , (pp_body, (iteratee, loopvar :: index_ids)) ) ;
    gensym_exit ()
  in
  match st with
  | SReal | SInt -> pp_body ppf (iteratee, index_ids)
  | SRowVector d | SVector d -> iter d pp_body
  | SMatrix (d1, d2) ->
      iter
        { expr= FunApp (StanLib, string_of_operator Times, [d1; d2])
        ; emeta= internal_meta }
        pp_body
  | SArray (t, d) ->
      iter d (fun ppf (i, idcs) ->
          pf ppf "%a" pp_block
            (pp_for_loop_iteratee ~index_ids:idcs, (i, t, pp_body)) )

let rec integer_el_type = function
  | SReal | SVector _ | SMatrix _ | SRowVector _ -> false
  | SInt -> true
  | SArray (st, _) -> integer_el_type st

let pp_decl ppf (vident, ut, adtype) =
  pf ppf "%a %s;" pp_unsizedtype_local (adtype, ut) vident

let pp_sized_decl ppf (vident, st, adtype) =
  pf ppf "%a@,%a" pp_decl
    (vident, remove_size st, adtype)
    pp_set_size (vident, st, adtype)

let pp_unused = fmt "(void) %s;  // suppress unused var warning@ "

let pp_function__ ppf (prog_name, fname) =
  pf ppf "static const char* function__ = %S;@ "
    (strf "%s_namespace::%s" prog_name fname) ;
  pp_unused ppf "function__"

let pp_located_msg ppf msg =
  pf ppf
    {|stan::lang::rethrow_located(
          std::runtime_error(std::string(%S) + ": " + e.what()), current_statement__);
      // Next line prevents compiler griping about no return
      throw std::runtime_error("*** IF YOU SEE THIS, PLEASE REPORT A BUG ***"); |}
    msg

let maybe_templated_arg_types (args : fun_arg_decl) =
  let is_autodiff (adtype, _, _) =
    match adtype with AutoDiffable -> true | _ -> false
  in
  List.filter ~f:is_autodiff args |> List.mapi ~f:(fun i _ -> sprintf "T%d__" i)

let%expect_test "arg types templated correctly" =
  [(AutoDiffable, "xreal", UReal); (DataOnly, "yint", UInt)]
  |> maybe_templated_arg_types |> String.concat ~sep:"," |> print_endline ;
  [%expect {| T0__ |}]

(** Pretty-prints a function's return-type, taking into account templated argument
    promotion.*)
let pp_returntype ppf arg_types rt =
  let scalar =
    strf "typename boost::math::tools::promote_args<@[<-35>%a@]>::type"
      (list ~sep:comma string)
      (maybe_templated_arg_types arg_types)
  in
  match rt with
  | Some ut -> pf ppf "%a@," pp_unsizedtype_custom_scalar (scalar, ut)
  | None -> pf ppf "void@,"

let pp_location ppf loc =
  ignore (loc : location_span) ;
  ignore ppf

(*
  pf ppf "current_statement__ = (char* )%S;@;"
    (string_of_location_span loc)
 *)

(** [pp_located_error ppf (pp_body_block, body_block, err_msg)] surrounds [body_block]
    with a C++ try-catch that will rethrow the error with the proper source location
    from the [body_block] (required to be a [stmt_loc Block] variant).*)
let pp_located_error ppf (pp_body_block, body, err_msg) =
  ignore err_msg ; pp_body_block ppf body

(*
  pf ppf "@ try %a" pp_body_block body ;
  string ppf " catch (const std::exception& e) " ;
  pp_block ppf (pp_located_msg, err_msg)
 *)

let math_fn_translations = function
  | FnPrint ->
      Some ("stan_print", [{expr= Var "pstream__"; emeta= internal_meta}])
  | FnLength -> Some ("length", [])
  | _ -> None

let trans_math_fn fname =
  Option.(
    value ~default:(fname, [])
      (bind (internal_fn_of_string fname) ~f:math_fn_translations))

let pp_arg ppf (custom_scalar, (_, name, ut)) =
  pf ppf "const %a& %s" pp_unsizedtype_custom_scalar (custom_scalar, ut) name

let rec pp_statement (ppf : Format.formatter)
    ({stmt; smeta} : (mtype_loc_ad, 'a) stmt_with) =
  let pp_stmt_list = list ~sep:cut pp_statement in
  match stmt with
  | Assignment (lhs, {expr= FunApp (CompilerInternal, f, _) as expr; emeta})
    when internal_fn_of_string f = Some FnReadData ->
      pp_statement ppf
        { stmt=
            Assignment
              ( lhs
              , {expr= Indexed ({expr; emeta}, [Single loop_bottom]); emeta} )
        ; smeta }
      (* XXX In stan2 this often generates:
                stan::model::assign(theta,
                            stan::model::cons_list(stan::model::index_uni(j), stan::model::nil_index_list()),
                            (mu + (tau * get_base1(theta_tilde,j,"theta_tilde",1))),
                            "assigning variable theta");
            }
        *)
  | Assignment ((assignee, idcs), rhs) ->
      pf ppf "%a = %a;" pp_indexed_simple (assignee, idcs) pp_expr rhs
  | TargetPE e -> pf ppf "lp_accum__.add(%a);" pp_expr e
  | NRFunApp (CompilerInternal, fname, {expr= Lit (Str, check_name); _} :: args)
    when fname = string_of_internal_fn FnCheck ->
      let args = {expr= Var "function__"; emeta= internal_meta} :: args in
      pp_statement ppf
        {stmt= NRFunApp (CompilerInternal, "check_" ^ check_name, args); smeta}
  | NRFunApp (CompilerInternal, fname, [var])
    when fname = string_of_internal_fn FnWriteParam ->
      pf ppf "vars__.push_back(@[<hov>%a@]);" pp_expr var
  | NRFunApp (CompilerInternal, fname, args) ->
      let fname, extra_args = trans_math_fn fname in
      pf ppf "%s(@[<hov>%a@]);" fname (list ~sep:comma pp_expr)
        (extra_args @ args)
  | NRFunApp (StanLib, fname, args) ->
      pf ppf "%s(@[<hov>%a@]);" fname (list ~sep:comma pp_expr) args
  | NRFunApp (UserDefined, fname, args) ->
      pf ppf "%s(@[<hov>%a@]);" fname (list ~sep:comma pp_expr) args
  | Break -> string ppf "break;"
  | Continue -> string ppf "continue;"
  | Return e -> pf ppf "return %a;" (option pp_expr) e
  | Skip -> ()
  | IfElse (cond, ifbranch, elsebranch) ->
      let pp_else ppf x = pf ppf "else %a" pp_statement x in
      pf ppf "if (@[<hov>%a@]) %a %a" pp_expr cond pp_block_s ifbranch
        (option pp_else) elsebranch
  | While (cond, body) ->
      pf ppf "while (@[<hov>%a@]) %a" pp_expr cond pp_block_s body
  | For
      { body=
          {stmt= Assignment (_, {expr= FunApp (CompilerInternal, f, _); _}); _}
          as body; _ }
    when internal_fn_of_string f = Some FnReadParam ->
      pp_statement ppf body
      (* Skip For loop part, just emit body due to the way FnReadParam emits *)
  | For {loopvar; lower; upper; body} ->
      pp_for_loop ppf (loopvar, lower, upper, pp_statement, body)
  | Block ls -> pp_block ppf (pp_stmt_list, ls)
  | SList ls -> pp_stmt_list ppf ls
  | Decl {decl_adtype; decl_id; decl_type} ->
      pp_sized_decl ppf (decl_id, decl_type, decl_adtype)

and pp_block_s ppf body =
  match body.stmt with
  | Block ls -> pp_block ppf (list ~sep:cut pp_statement, ls)
  | _ -> pp_block ppf (pp_statement, body)

(** [pp_located_error_b] automatically adds a Block wrapper *)
let pp_located_error_b ppf (body_stmts, err_msg) =
  pp_located_error ppf
    (pp_statement, {stmt= Block body_stmts; smeta= no_span}, err_msg)

let pp_fun_def ppf = function
  | {fdrt; fdname; fdargs; fdbody; _} -> (
      let argtypetemplates =
        List.mapi ~f:(fun i _ -> sprintf "T%d__" i) fdargs
      in
      let pp_body ppf fdbody =
        let text = pf ppf "%s@;" in
        pf ppf
          "@[<hv 8>typedef typename \
           boost::math::tools::promote_args<%a>::type local_scalar_t__;@]@,"
          (list ~sep:comma string) argtypetemplates ;
        text "typedef local_scalar_t__ fun_return_scalar_t__;" ;
        text "const static bool propto__ = true;" ;
        text "(void) propto__;" ;
        text
          "local_scalar_t__ \
           DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());" ;
        pp_unused ppf "DUMMY_VAR__" ;
        pp_located_error ppf (pp_statement, fdbody, "inside UDF " ^ fdname) ;
        pf ppf "@ "
      in
      pf ppf "@[<hov>template <%a>@]@ "
        (list ~sep:comma (fmt "typename %s"))
        argtypetemplates ;
      pp_returntype ppf fdargs fdrt ;
      pf ppf "%s(@[<hov>%a" fdname (list ~sep:comma pp_arg)
        (List.zip_exn argtypetemplates fdargs) ;
      pf ppf ", std::ostream* pstream__@]) " ;
      match fdbody.stmt with
      | Skip -> pf ppf ";@ "
      | _ -> pp_block ppf (pp_body, fdbody) )

let%expect_test "location propagates" =
  let loc1 = {no_span with begin_loc= {no_loc with filename= "HI"}} in
  let loc2 = {no_span with begin_loc= {no_loc with filename= "LO"}} in
  { smeta= loc1
  ; stmt=
      Block
        [ { stmt= NRFunApp (CompilerInternal, string_of_internal_fn FnPrint, [])
          ; smeta= loc2 } ] }
  |> strf "@[<v>%a@]" pp_statement
  |> print_endline ;
  [%expect {|
    {
      stan_print(pstream__);
    } |}]

let version = "// Code generated by Stan version 2.18.0"
let includes = "#include <stan/model/model_header.hpp>"

let rec basetype = function
  | UInt -> "int"
  | UReal -> "double"
  | UArray t -> basetype t
  | UMatrix -> "matrix_d"
  | URowVector -> "row_vector_d"
  | UVector -> "vector_d"
  | x -> raise_s [%message "basetype not defined for " (x : unsizedtype)]

let var_context_container st =
  match basetype (remove_size st) with "int" -> "vals_i" | _ -> "vals_r"

let rec get_dims = function
  | SInt | SReal -> []
  | SVector d | SRowVector d -> [d]
  | SMatrix (dim1, dim2) -> [dim1; dim2]
  | SArray (t, dim) -> dim :: get_dims t

let%expect_test "dims" =
  let v s = {expr= Var s; emeta= internal_meta} in
  strf "@[%a@]" (list ~sep:comma pp_expr)
    (get_dims (SArray (SMatrix (v "x", v "y"), v "z")))
  |> print_endline ;
  [%expect {| z, x, y |}]

(* Read in data steps:
   1. context__.validate_dims() (what is this?)
   1. find vals_%s__ from context__.vals_%s(vident)
   1. keep track of pos__
   1. run checks on resulting vident
*)

let pp_ctor ppf (p : typed_prog) =
  let params =
    [ "stan::io::var_context& context__"; "unsigned int random_seed__ = 0"
    ; "std::ostream* pstream__ = nullptr" ]
  in
  pf ppf "%s(@[<hov 0>%a) : prob_grad(0) @]" p.prog_name
    (list ~sep:comma string) params ;
  let pp_mul ppf () = pf ppf " * " in
  let pp_num_param ppf dims =
    pf ppf "num_params_r__ += %a;" (list ~sep:pp_mul pp_expr) dims
  in
  let get_param_st = function
    | _, (st, Parameters) -> (
      match get_dims st with
      | [] -> Some [{expr= Lit (Int, "1"); emeta= internal_meta}]
      | ls -> Some ls )
    | _ -> None
  in
  let rec pp_statement_zeroing ppf s =
    match s.stmt with
    | Decl {decl_id; decl_type; _} ->
        pp_set_size ppf (decl_id, decl_type, DataOnly)
    | Block ls | SList ls -> (list ~sep:cut pp_statement_zeroing) ppf ls
    | _ -> pp_statement ppf s
  in
  pp_block ppf
    ( (fun ppf p ->
        pf ppf "typedef double local_scalar_t__;@ " ;
        pf ppf "boost::ecuyer1988 base_rng__ = @ " ;
        pf ppf "    stan::services::util::create_rng(random_seed__, 0);@ " ;
        pp_unused ppf "base_rng__" ;
        pp_function__ ppf (p.prog_name, p.prog_name) ;
        pp_located_error ppf
          ( pp_statement_zeroing
          , {stmt= Block p.prepare_data; smeta= no_span}
          , "inside ctor" ) ;
        cut ppf () ;
        pf ppf "num_params_r__ = 0U;@ " ;
        pf ppf "%a@ "
          (list ~sep:cut pp_num_param)
          (List.filter_map ~f:get_param_st p.output_vars) )
    , p )

let pp_model_private ppf p =
  let data_decl = function
    | decl_id, (st, Data) -> Some (decl_id, remove_size st, DataOnly)
    | _ -> None
  in
  let data_decls = List.filter_map ~f:data_decl p.input_vars in
  pf ppf "%a" (list ~sep:cut pp_decl) data_decls

let pp_method ppf rt name params intro ?(outro = []) ppbody =
  pf ppf "@[<v 2>%s %a const " rt pp_call_str (name, params) ;
  pf ppf "{@,%a" (list ~sep:cut string) intro ;
  pf ppf "@ " ;
  ppbody ppf ;
  if not (List.is_empty outro) then pf ppf "@ %a" (list ~sep:cut string) outro ;
  pf ppf "@,} // %s() @,@]" name

let pp_get_param_names ppf p =
  let add_param = fmt "names__.push_back(%S);" in
  pp_method ppf "void" "get_param_names" ["std::vector<std::string>& names__"]
    [] (fun ppf ->
      pf ppf "names__.resize(0);@ " ;
      (list ~sep:cut add_param) ppf (List.map ~f:fst p.output_vars) )

let pp_get_dims ppf p =
  let pp_dim ppf dim = pf ppf "dims__.push_back(%a);@," pp_expr dim in
  let pp_dim_sep ppf () =
    pf ppf "dimss__.push_back(dims__);@,dims__.resize(0);@,"
  in
  let pp_output_var ppf =
    (list ~sep:pp_dim_sep (list ~sep:cut pp_dim))
      ppf
      List.(map ~f:get_dims (map ~f:(fun (_, (st, _)) -> st) p.output_vars))
  in
  let params = ["std::vector<std::vector<size_t>>& dimss__"] in
  pp_method ppf "void" "get_dims" params
    ["dimss__.resize(0);"; "std::vector<size_t> dims__;"] (fun ppf ->
      pp_output_var ppf ; pp_dim_sep ppf () )

let pp_method_b ppf rt name params intro ?(outro = []) body =
  pp_method ppf rt name params intro
    (fun ppf -> pp_located_error_b ppf (body, "inside " ^ name))
    ~outro

let pp_write_array ppf p =
  pf ppf "template <typename RNG>@ " ;
  let params =
    [ "RNG& base_rng"; "std::vector<double>& params_r__"
    ; "std::vector<int>& params_i__"; "std::vector<double>& vars__"
    ; "bool emit_transformed_parameters__ = true"
    ; "bool emit_generated_quantities__ = true"; "std::ostream* pstream__ = 0"
    ]
  in
  let intro =
    [ "typedef double local_scalar_t__;"; "vars__.resize(0);"
    ; "stan::io::reader<local_scalar_t__> in__(params_r__, params_i__);"
    ; strf "%a" pp_function__ (p.prog_name, "write_array")
    ; strf "%a" pp_unused "function__" ]
  in
  pp_method_b ppf "void" "write_array" params intro p.generate_quantities

let separated_output_vars p =
  List.partition3_map
    ~f:(function
      | id, (st, Parameters) -> `Fst (id, st)
      | id, (st, TransformedParameters) -> `Snd (id, st)
      | id, (st, GeneratedQuantities) -> `Trd (id, st)
      | _ -> raise_s [%message "Why is there data in output_vars"])
    p.output_vars

let pp_string_lit = fmt "%S"

let pp_constrained_param_names ppf p =
  let params =
    [ "std::vector<std::string>& param_names__"
    ; "bool emit_transformed_parameters__ = true"
    ; "bool emit_generated_quantities__ = true" ]
  in
  let paramvars, tparamvars, gqvars = separated_output_vars p in
  let emit_name ppf (name, idcs) =
    let to_string = fmt "std::to_string(%s)" in
    pf ppf "param_names__.push_back(std::string() + %a);"
      (list ~sep:(fun ppf () -> pf ppf " + '.' + ") string)
      (strf "%S" name :: List.map ~f:(strf "%a" to_string) idcs)
  in
  let pp_param_names ppf (decl_id, st) =
    pp_for_loop_iteratee ppf (decl_id, st, emit_name)
  in
  pp_method ppf "void" "constrained_param_names" params [] (fun ppf ->
      (list ~sep:cut pp_param_names) ppf paramvars ;
      pf ppf "@,if (emit_transformed_parameters__) %a@," pp_block
        (list ~sep:cut pp_param_names, tparamvars) ;
      pf ppf "@,if (emit_generated_quantities__) %a@," pp_block
        (list ~sep:cut pp_param_names, gqvars) )

(* XXX This is just a copy of constrained, I need to figure out which one is wrong
   and fix it eventually. *)
let pp_unconstrained_param_names ppf p =
  let params =
    [ "std::vector<std::string>& param_names__"
    ; "bool emit_transformed_parameters__ = true"
    ; "bool emit_generated_quantities__ = true" ]
  in
  let paramvars, tparamvars, gqvars = separated_output_vars p in
  let emit_name ppf (name, idcs) =
    let to_string = fmt "std::to_string(%s)" in
    pf ppf "param_names__.push_back(std::string() + %a);"
      (list ~sep:(fun ppf () -> pf ppf " + '.' + ") string)
      (strf "%S" name :: List.map ~f:(strf "%a" to_string) idcs)
  in
  let pp_param_names ppf (decl_id, st) =
    pp_for_loop_iteratee ppf (decl_id, st, emit_name)
  in
  pp_method ppf "void" "unconstrained_param_names" params [] (fun ppf ->
      (list ~sep:cut pp_param_names) ppf paramvars ;
      pf ppf "@,if (emit_transformed_parameters__) %a@," pp_block
        (list ~sep:cut pp_param_names, tparamvars) ;
      pf ppf "@,if (emit_generated_quantities__) %a@," pp_block
        (list ~sep:cut pp_param_names, gqvars) )

let pp_transform_inits ppf p =
  let params =
    [ "const stan::io::var_context& context__"; "std::vector<int>& params_i__"
    ; "std::vector<double>& params_r__"; "std::ostream* pstream__" ]
  in
  let intro =
    [ "typedef double local_scalar_t__;"
    ; "stan::io::writer<double> writer__(params_r__, params_i__);"
    ; "std::vector<double> vals_r__;"; "std::vector<int> vals_i__;" ]
  in
  pp_method_b ppf "void" "transform_inits" params intro p.transform_inits

let pp_fndef_sig ppf (rt, fname, params) =
  pf ppf "%s %s(@[<hov>%a@])" rt fname (list ~sep:comma string) params

let pp_log_prob ppf p =
  pf ppf "template <bool propto__, bool jacobian__, typename T__>@ " ;
  let params =
    [ "std::vector<T__>& params_r__"; "std::vector<int>& params_i__"
    ; "std::ostream* pstream__ = 0" ]
  in
  let intro =
    [ "typedef T__ local_scalar_t__;"
    ; "local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());"
    ; strf "%a" pp_unused "DUMMY_VAR__"
    ; "T__ lp__(0.0);"; "stan::math::accumulator<T__> lp_accum__;"
    ; "stan::io::reader<local_scalar_t__> in__(params_r__, params_i__);" ]
  in
  let outro = ["lp_accum__.add(lp__);"; "return lp_accum__.sum();"] in
  let log_prob =
    List.map
      ~f:(fun {stmt; smeta} ->
        match stmt with
        | Assignment (lhs, {expr= FunApp (CompilerInternal, f, args); emeta})
          when internal_fn_of_string f = Some FnConstrain ->
            let var n = {expr= Var n; emeta= internal_meta} in
            let assign rhs = {stmt= Assignment (lhs, rhs); smeta} in
            { stmt=
                IfElse
                  ( var "jacobian__"
                  , assign
                      { expr= FunApp (CompilerInternal, f, args @ [var "lp__"])
                      ; emeta }
                  , Some
                      (assign {expr= FunApp (CompilerInternal, f, args); emeta})
                  )
            ; smeta }
        | _ -> {stmt; smeta} )
      p.log_prob
  in
  pp_method_b ppf "T__" "log_prob" params intro log_prob ~outro

let pp_overloads ppf () =
  pf ppf
    {|
    template <typename RNG>
    void write_array(RNG& base_rng,
                     Eigen::Matrix<double,Eigen::Dynamic,1>& params_r,
                     Eigen::Matrix<double,Eigen::Dynamic,1>& vars,
                     bool emit_transformed_parameters__ = true,
                     bool emit_generated_quantities__ = true,
                     std::ostream* pstream = 0) const {
      std::vector<double> params_r_vec(params_r.size());
      for (int i = 0; i < params_r.size(); ++i)
        params_r_vec[i] = params_r(i);
      std::vector<double> vars_vec;
      std::vector<int> params_i_vec;
      write_array(base_rng, params_r_vec, params_i_vec, vars_vec,
          emit_transformed_parameters__, emit_generated_quantities__, pstream);
      vars.resize(vars_vec.size());
      for (int i = 0; i < vars.size(); ++i)
        vars(i) = vars_vec[i];
    }

    template <bool propto__, bool jacobian__, typename T_>
    T_ log_prob(Eigen::Matrix<T_,Eigen::Dynamic,1>& params_r,
               std::ostream* pstream = 0) const {
      std::vector<T_> vec_params_r;
      vec_params_r.reserve(params_r.size());
      for (int i = 0; i < params_r.size(); ++i)
        vec_params_r.push_back(params_r(i));
      std::vector<int> vec_params_i;
      return log_prob<propto__,jacobian__,T_>(vec_params_r, vec_params_i, pstream);
    }
|}

let pp_model_public ppf p =
  pf ppf "@ %a" pp_ctor p ;
  pf ppf "@ %a" pp_log_prob p ;
  pf ppf "@ %a" pp_get_param_names p ;
  pf ppf "@ %a" pp_get_dims p ;
  pf ppf "@ %a" pp_write_array p ;
  pf ppf "@ %a" pp_constrained_param_names p ;
  pf ppf "@ %a" pp_unconstrained_param_names p ;
  pf ppf "@ %a" pp_transform_inits p ;
  pf ppf "@ %a" pp_overloads ()

let pp_model ppf (p : typed_prog) =
  pf ppf "class %s : public prob_grad {" p.prog_name ;
  pf ppf "@ @[<v 1>@ private:@ @[<v 1> %a@]@ " pp_model_private p ;
  pf ppf "@ public:@ @[<v 1> ~%s() { }" p.prog_name ;
  pf ppf "@ @ static std::string model_name() { return \"%s\"; }" p.prog_name ;
  pf ppf "@ %a@]@]@ };" pp_model_public p

let globals = "static char* current_statement__;"

let usings =
  {|
using std::istream;
using std::string;
using std::stringstream;
using std::vector;
using stan::io::dump;
using stan::math::lgamma;
using stan::model::prob_grad;
using namespace stan::math; |}

let pp_prog ppf (p : (mtype_loc_ad with_expr, stmt_loc) prog) =
  pf ppf "@[<v>@ %s@ %s@ namespace %s_namespace {@ %s@ %s@ %a@ %a@ }@ @]"
    version includes p.prog_name usings globals (list ~sep:cut pp_fun_def)
    p.functions_block pp_model p ;
  pf ppf "@,typedef %s_namespace::%s stan_model;@," p.prog_name p.prog_name

let%expect_test "udf" =
  let with_no_loc stmt = {stmt; smeta= no_span} in
  let w e = {expr= e; emeta= internal_meta} in
  { fdrt= None
  ; fdname= "sars"
  ; fdargs= [(DataOnly, "x", UMatrix); (AutoDiffable, "y", URowVector)]
  ; fdbody=
      Return
        (Some
           (w @@ FunApp (StanLib, "add", [w @@ Var "x"; w @@ Lit (Int, "1")])))
      |> with_no_loc |> List.return |> Block |> with_no_loc
  ; fdloc= no_span }
  |> strf "@[<v>%a" pp_fun_def |> print_endline ;
  [%expect
    {|
    template <typename T0__, typename T1__>
    void
    sars(const Eigen::Matrix<T0__, -1, -1>& x,
         const Eigen::Matrix<T1__, 1, -1>& y, std::ostream* pstream__) {
      typedef typename boost::math::tools::promote_args<T0__,
              T1__>::type local_scalar_t__;
      typedef local_scalar_t__ fun_return_scalar_t__;
      const static bool propto__ = true;
      (void) propto__;
      local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());
      (void) DUMMY_VAR__;  // suppress unused var warning
      {
        return add(x, 1);
      }

    } |}]
