open Core_kernel
open Middle
open Middle.Expr

let get_decl_dims Stmt.Fixed.({pattern; _}) =
  match pattern with
  | Stmt.Fixed.Pattern.Decl
      { decl_adtype= UnsizedType.AutoDiffable
      ; decl_id
      ; decl_type= Type.Sized sized_type } ->
      Some (decl_id, SizedType.get_dims sized_type)
  | _ -> None

(**
 * Apply an op returning a Set of strings for `Index` types
 *  with inner expressions
 * @param op a functor returning a Set of strings
 * @param ind the Index.t to modify
 *)
let map_index (op : Typed.Meta.t Expr.Fixed.t -> string Core_kernel.Set.Poly.t)
    (ind : Typed.Meta.t Expr.Fixed.t Index.t) : string Set.Poly.t =
  match ind with
  | Index.All -> Set.Poly.empty
  | Single ind_expr -> op ind_expr
  | Upfrom ind_expr -> op ind_expr
  | Between (expr_top, expr_bottom) ->
      Set.Poly.union (op expr_top) (op expr_bottom)
  | MultiIndex exprs -> op exprs

(** 
 * Modify the expressions to demote/promote from AoS <-> SoA and vice versa
 * The only real path in the below is on the functions.
 *
 * For AoS, we check that all of the matrix and vector names
 *  in the list of expressions are in the `modifiable_set` and if so
 *  make the function AoS. 
 * For SoA, we check that any of the matrix and vector names
 *  in the list of expressions are in the `modifiable_set` and if so
 *  make the function SoA. 
 * @param mem_pattern The memory pattern to change functions to.
 * @param modifiable_set The name of the variables whose
 *  associated expressions we want to modify.
 * @param pattern The expression to modify
 *)
let rec modify_expr_pattern
    (pattern : Typed.Meta.t Expr.Fixed.t Fixed.Pattern.t) =
  let mod_expr = modify_expr in
  match pattern with
  | Expr.Fixed.Pattern.FunApp (_, (_ : Typed.Meta.t Expr.Fixed.t list)) ->
      pattern
  | TernaryIf (predicate, texpr, fexpr) ->
      TernaryIf (mod_expr predicate, mod_expr texpr, mod_expr fexpr)
  | Indexed (idx_expr, indexed) ->
      Indexed (mod_expr idx_expr, List.map ~f:(Index.map mod_expr) indexed)
  | EAnd (lhs, rhs) -> EAnd (mod_expr lhs, mod_expr rhs)
  | EOr (lhs, rhs) -> EOr (mod_expr lhs, mod_expr rhs)
  | Var (_ : string) | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) ->
      pattern

(** 
 * Given a Set of strings containing the names of objects that can be 
 * promoted from AoS -> SoA for a given expression, promote them.
 * @param mem_pattern The memory pattern to change expressions to.
 * @param modifiable_set The name of the variables whose
 *  associated expressions we want to modify.
 *)
and modify_expr (Expr.Fixed.({pattern; _}) as expr) =
  let new_pattern = modify_expr_pattern pattern in
  {expr with pattern= new_pattern}

(**
 * Modify statement patterns in the MIR from AoS <-> SoA and vice versa 
 * @param mem_pattern A mem_pattern to modify expressions to. For the 
 *  given memory pattern, this modifies 
 *  statement patterns and expressions to it.
 * @param pattern The statement pattern to modify 
 * @param modifiable_set The name of the variable we are searching for.
 *)

(*
let rec modify_stmt_pattern 
    (pattern :
      ( Typed.Meta.t Expr.Fixed.t
      , (Typed.Meta.t, Stmt.Located.Meta.t) Stmt.Fixed.t )
      Stmt.Fixed.Pattern.t)  =
  let mod_expr =
    Mir_utils.map_rec_expr (modify_expr_pattern )
  in
  let mod_stmt stmt = 
    match modify_stmt stmt with 
    | [a] -> a
    | _ -> raise_s
    [%message ( "Should not happen!!!" : string )]  in
  (*let printer intro s = Set.Poly.iter ~f:(printf intro) s in*)
  match pattern with
  | Stmt.Fixed.Pattern.NRFunApp (_, (_ : Typed.Meta.t Expr.Fixed.t list)) -> pattern
  | Assignment (((name : string), (ut : UnsizedType.t), lhs), rhs) ->
      Assignment
        ((name, ut, List.map ~f:(Index.map mod_expr) lhs), mod_expr rhs)
  | IfElse (predicate, true_stmt, op_false_stmt) ->
      IfElse
        ( mod_expr predicate
        , mod_stmt true_stmt
        , Option.map ~f:mod_stmt op_false_stmt )
  | Block stmts -> Block (List.map ~f:mod_stmt stmts)
  | SList stmts -> SList (List.map ~f:mod_stmt stmts)
  | For ({lower; upper; body; _} as loop) ->
      Stmt.Fixed.Pattern.For
        { loop with
          lower= mod_expr lower; upper= mod_expr upper; body= mod_stmt body }
  | TargetPE expr -> TargetPE (mod_expr expr)
  | Return optional_expr -> Return (Option.map ~f:mod_expr optional_expr)
  | Profile ((a : string), stmt) -> Profile (a, List.map ~f:mod_stmt stmt)
  | While (predicate, body) -> While (mod_expr predicate, mod_stmt body)
  | Skip | Break | Continue | Decl _ -> pattern
*)

let rec promote_single_idx_to_any_expr loopvar
    (Expr.Fixed.({pattern; _}) as expr) =
  let promote_expr = promote_single_idx_to_any_expr loopvar in
  let new_pattern =
    match pattern with
    | Expr.Fixed.Pattern.FunApp (a, (exprs : Typed.Meta.t Expr.Fixed.t list))
      ->
        Expr.Fixed.Pattern.FunApp (a, List.map ~f:promote_expr exprs)
    | TernaryIf (predicate, true_expr, false_expr) ->
        TernaryIf
          ( promote_expr predicate
          , promote_expr true_expr
          , promote_expr false_expr )
    | Indexed (idx_expr, indexed) -> Indexed (promote_expr idx_expr, indexed)
    | EAnd (lhs, rhs) -> EAnd (promote_expr lhs, promote_expr rhs)
    | EOr (lhs, rhs) -> EOr (promote_expr lhs, promote_expr rhs)
    | Var (a : string) -> Var a
    | Lit ((a : Expr.Fixed.Pattern.litType), (b : string)) -> Lit (a, b)
  in
  {expr with pattern= new_pattern}

and promote_single_idx_to_any_index loopvar idx =
  let promote_expr = promote_single_idx_to_any_expr loopvar in
  match idx with
  | Index.All -> Index.All
  | Single Expr.Fixed.({pattern= Var a; _}) when loopvar = a -> Index.All
  | Single ind_expr -> Single (promote_expr ind_expr)
  | Upfrom ind_expr -> Upfrom (promote_expr ind_expr)
  | Between (expr_top, expr_bottom) ->
      Between (promote_expr expr_top, promote_expr expr_bottom)
  | MultiIndex expr -> MultiIndex (promote_expr expr)

let rec check_index_expr loopvar Expr.Fixed.({pattern; _}) =
  let check_expr = check_index_expr loopvar in
  let lst_check_expr = List.for_all ~f:check_expr in
  match pattern with
  | Expr.Fixed.Pattern.FunApp (kind, (exprs : Typed.Meta.t Expr.Fixed.t list))
    ->
      let find_args
          Expr.Fixed.({meta= Expr.Typed.Meta.({type_; adlevel; _}); _}) =
        (adlevel, type_)
      in
      let new_exprs =
        List.map ~f:(promote_single_idx_to_any_expr loopvar) exprs
      in
      let is_fun_support =
        match kind with
        | StanLib (name, _) -> (
          match
            Stan_math_signatures.stan_math_returntype name
              (List.map ~f:find_args new_exprs)
          with
          | Some _ -> true
          | None -> false )
        | _ -> false
      in
      lst_check_expr exprs && is_fun_support
  | TernaryIf _ -> false
  | Indexed (idx_expr, indexed) ->
      check_expr idx_expr && List.for_all ~f:(check_indexing loopvar) indexed
  | EAnd _ -> false
  | EOr _ -> false
  | Var (_ : string) | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) ->
      true

and check_indexing loopvar idx =
  match idx with
  | Index.Single Expr.Fixed.({pattern= Var first; _}) when first = loopvar ->
      true
  | Index.Single a -> check_index_expr loopvar a
  | _ -> false

let rec get_assignments ((loopvar, _, _) as meta_info)
    (Stmt.Fixed.({pattern; _}) as stmt) : 'a Option.t =
  let new_stmts lst_stmts =
    List.filter_map ~f:(get_assignments meta_info) lst_stmts
  in
  match pattern with
  | Stmt.Fixed.Pattern.NRFunApp (_, (_ : Typed.Meta.t Expr.Fixed.t list)) ->
      None
  | Assignment (((_ : string), (_ : UnsizedType.t), lhs), rhs) ->
      if
        List.for_all ~f:(check_indexing loopvar) lhs
        && check_index_expr loopvar rhs
      then Some stmt
      else None
  | IfElse _ -> None
  | Block stmts ->
      Some {stmt with pattern= Stmt.Fixed.Pattern.Block (new_stmts stmts)}
  | SList stmts -> Some {stmt with pattern= SList (new_stmts stmts)}
  | For _ -> None (*idk how to deal with this yet*)
  | TargetPE _ -> None (* Could also do these*)
  | Return _ -> None (*Nah?*)
  | Profile _ -> None
  | While _ -> None
  | Skip | Break | Continue | Decl _ -> None

let find_loop_pattern
    pattern  =
  (*let printer intro s = Set.Poly.iter ~f:(printf intro) s in*)
  match pattern with
  | Stmt.Fixed.Pattern.For {loopvar; lower; upper; body} ->
      get_assignments (loopvar, lower, upper) body
  | Skip | Break | Continue | Decl _ | Assignment _ | IfElse _ | Block _ | _ ->
      None

let strip_indices expr _ _ = expr

(*
let rec gen_new_stmts del_stmt_lst old_stmt_lst = 
  let del_stmt_filt old_stmt del_stmt = 
  (match delete_stmts old_stmt del_stmt with 
  | Some undel_stmt -> undel_stmt 
  | None -> old_stmt ) in
  let per_old old_stmt = List.fold_left ~f:del_stmt_filt old_stmt del_stmt_lst
in 
List.map ~f:per_old old_stmt_lst
*)

let delete_stmts ((Stmt.Fixed.({pattern; _}) as stmt) : (Typed.Meta.t, Stmt.Located.t) Stmt.Fixed.t)
(Stmt.Fixed.({pattern = del_pattern; _}) : (Typed.Meta.t, Stmt.Located.t) Stmt.Fixed.t) : ('a, 'b) Stmt.Fixed.t Option.t =
  match (del_pattern, pattern) with
  | Assignment (_, _), (Assignment (_, _) as assign) when assign = del_pattern
    ->
      None
  | Block _, Block stmts ->
      Some {stmt with pattern= Stmt.Fixed.Pattern.Block stmts}
  | SList _, SList stmts ->
      Some {stmt with pattern= SList (stmts)}
  | _, For _ -> Some stmt (*idk how to deal with this yet*)
  | _, TargetPE _ -> Some stmt (* Could also do these*)
  | _, Return _ -> Some stmt (*Nah?*)
  | _, While _ -> Some stmt
  | _, Assignment _ -> Some stmt
  | _, IfElse _ -> Some stmt
  | _, Stmt.Fixed.Pattern.NRFunApp (_, (_ : Typed.Meta.t Expr.Fixed.t list)) ->
      Some stmt
  | _, (Profile _ | Skip | Break | Continue | Decl _ | Block _ | SList _) ->
      Some stmt

let gen_new_stmt assignee ut lhs rhs loop_idx _ =
  Stmt.Fixed.Pattern.Assignment
    ( (assignee, ut, List.map ~f:(promote_single_idx_to_any_index loop_idx) lhs)
    , promote_single_idx_to_any_expr loop_idx rhs )

let modify_stmt ((Stmt.Fixed.({pattern; _}) as stmt) : Stmt.Located.t) =
  match find_loop_pattern pattern with
  | Some _ -> [stmt] 
  | None -> [stmt]

let rec collapse_looper top_lvl_decls (top_list : Stmt.Located.t option) rest_of_list =
  match (top_list, rest_of_list) with
  | Some top, Some bottom ->
      List.concat [modify_stmt top; collapse_loops top_lvl_decls bottom]
  | None, Some bottom -> collapse_loops top_lvl_decls bottom
  | Some top, None -> modify_stmt top
  | None, None -> []

and collapse_loops top_lvl_decls mir =
  collapse_looper top_lvl_decls (List.hd mir) (List.tl mir)
