open Core_kernel
open Middle
open Middle.Expr
open Dataflow_types

(**
 * Modify an index's inner expressions with `op`
 * @param op a functor returning an expression
 * @param ind the Index.t to modify
 *)
let mod_index op ind =
  match ind with
  | Index.All -> Index.All
  | Single ind_expr -> Single (op ind_expr)
  | Upfrom ind_expr -> Upfrom (op ind_expr)
  | Between (expr_top, expr_bottom) -> Between (op expr_top, op expr_bottom)
  | MultiIndex exprs -> MultiIndex (op exprs)

(**
 * Apply an op returning true/false to an index 
 * @param op a functor returning a boolean
 * @param ind the Index.t to modify
 *)
let search_index success_lst op ind =
  match ind with
  | Index.All -> success_lst
  | Single ind_expr -> op ind_expr
  | Upfrom ind_expr -> op ind_expr
  | Between (expr_top, expr_bottom) ->
      Set.Poly.inter (op expr_top) (op expr_bottom)
  | MultiIndex exprs -> op exprs

let get_index_names op ind =
  match ind with
  | Index.All -> Set.Poly.empty
  | Single ind_expr -> op ind_expr
  | Upfrom ind_expr -> op ind_expr
  | Between (expr_top, expr_bottom) ->
      Set.Poly.union (op expr_top) (op expr_bottom)
  | MultiIndex exprs -> op exprs

let find_index op ind =
  match ind with
  | Index.All -> true
  | Single ind_expr -> op ind_expr
  | Upfrom ind_expr -> op ind_expr
  | Between (expr_top, expr_bottom) -> op expr_top || op expr_bottom
  | MultiIndex exprs -> op exprs

(**
 * Search through an expression for `Var name` where `name = var_name`
 * @param var_name A string with the name of the obj
 *  we are searching for.
 * @param pattern An expression pattern we recursivly search through 
 *  for the name.
 **)
let rec query_aos_names success_lst Expr.Fixed.({pattern; _}) =
  let query_name = query_aos_names success_lst in
  match pattern with
  | FunApp (_, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      List.exists ~f:query_name exprs
  | TernaryIf (predicate, texpr, fexpr) ->
      query_name predicate || query_name texpr || query_name fexpr
  | Indexed (expr, indexed) ->
      let find_index = find_index query_name in
      query_name expr || List.exists ~f:find_index indexed
  | Var (name : string) -> Set.Poly.mem success_lst name
  | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) -> false
  | EAnd (lhs, rhs) | EOr (lhs, rhs) -> query_name lhs || query_name rhs

let rec remove_aos_names success_lst Expr.Fixed.({pattern; _}) =
  let query_name = remove_aos_names success_lst in
  match pattern with
  | FunApp (_, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      Set.Poly.union_list (List.map ~f:query_name exprs)
  | TernaryIf (predicate, texpr, fexpr) ->
      Set.Poly.inter
        (Set.Poly.inter (query_name predicate) (query_name texpr))
        (query_name fexpr)
  | Indexed (expr, indexed) ->
      let search_index = search_index success_lst query_name in
      Set.Poly.inter (query_name expr)
        (Set.Poly.union_list (List.map ~f:search_index indexed))
  | Var (name : string) -> Set.Poly.remove success_lst name
  | Lit ((_ : Expr.Fixed.Pattern.litType), (name : string)) ->
      Set.Poly.remove success_lst name
  | EAnd (lhs, rhs) | EOr (lhs, rhs) ->
      Set.Poly.inter (query_name lhs) (query_name rhs)

(**
 * Search through an expression for `Var name` where `name = var_name`
 * @param var_name A Set of strings with the name of the obj
 *  we are searching for.
 * @param pattern An expression pattern we recursivly search through 
 *  for the name.
 **)
let rec query_aos_set_names (var_name : string Set.Poly.t)
    Expr.Fixed.({pattern; _}) =
  let query_name = query_aos_set_names var_name in
  match pattern with
  | FunApp (_, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      List.exists ~f:query_name exprs
  | TernaryIf (predicate, texpr, fexpr) ->
      query_name predicate || query_name texpr || query_name fexpr
  | Indexed (expr, indexed) ->
      let find_index = find_index query_name in
      query_name expr || List.exists ~f:find_index indexed
  | Var (name : string) -> Set.Poly.exists ~f:(fun x -> x = name) var_name
  | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) -> false
  | EAnd (lhs, rhs) | EOr (lhs, rhs) -> query_name lhs || query_name rhs

let rec get_aos_set_names Expr.Fixed.({pattern; _}) =
  let query_name = get_aos_set_names in
  match pattern with
  | FunApp (_, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      Set.Poly.union_list (List.map ~f:query_name exprs)
  | TernaryIf (predicate, texpr, fexpr) ->
      Set.Poly.union
        (Set.Poly.union (query_name predicate) (query_name texpr))
        (query_name fexpr)
  | Indexed (expr, indexed) ->
      let search_index = get_index_names query_name in
      Set.Poly.union (query_name expr)
        (Set.Poly.union_list (List.map ~f:search_index indexed))
  | Var (name : string) -> Set.Poly.singleton name
  | Lit ((_ : Expr.Fixed.Pattern.litType), (name : string)) ->
      Set.Poly.singleton name
  | EAnd (lhs, rhs) | EOr (lhs, rhs) ->
      Set.Poly.union (query_name lhs) (query_name rhs)

let rec remove_aos_set_names (success_lst : string Set.Poly.t)
    Expr.Fixed.({pattern; _}) =
  let query_name = remove_aos_set_names success_lst in
  match pattern with
  | FunApp (_, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      Set.Poly.union_list (List.map ~f:query_name exprs)
  | TernaryIf (predicate, texpr, fexpr) ->
      Set.Poly.inter
        (Set.Poly.inter (query_name predicate) (query_name texpr))
        (query_name fexpr)
  | Indexed (expr, indexed) ->
      let search_index = search_index success_lst query_name in
      Set.Poly.inter (query_name expr)
        (Set.Poly.union_list (List.map ~f:search_index indexed))
  | Var (name : string) -> Set.Poly.remove success_lst name
  | Lit ((_ : Expr.Fixed.Pattern.litType), (name : string)) ->
      Set.Poly.remove success_lst name
  | EAnd (lhs, rhs) | EOr (lhs, rhs) ->
      Set.Poly.inter (query_name lhs) (query_name rhs)

(** 
 * Modify functions expressions from SoA to AoS
 * TODO: Docs
 * The main issue with this right now is that if we see the failed var_name
 * inside of any StanLib we flip the whole StanLib to AoS, but we only need to 
 * do that if every expression's objs are all AoS. If just one argument 
 * is still an SoA then we can actually keep the functions as SoA.
 *
 * The only real path in the below is on the functions, everything else is 
 * for recursion through expressions of expressions.
 *
 * @param var_name The name of the variable whose
 *  associated expressions we want to modify.
 * @param expr The expression to modify
 *)
let rec modify_soa_exprs (var_name : string Set.Poly.t)
    (Expr.Fixed.({pattern; _}) as expr) =
  let mod_expr = modify_soa_exprs var_name in
  let find_name = query_aos_set_names var_name in
  let new_pattern =
    match pattern with
    | FunApp (kind, (exprs : 'a Expr.Fixed.t list)) ->
        let exprs' = List.map ~f:mod_expr exprs in
        let modify_funs kind =
          match kind with
          | Fun_kind.StanLib (name, sfx, Common.Helpers.AoS) as func -> (
            match List.exists ~f:find_name exprs with
            | true -> Fun_kind.StanLib (name, sfx, Common.Helpers.SoA)
            | false -> func )
          | _ -> kind
        in
        Expr.Fixed.Pattern.FunApp (modify_funs kind, exprs')
    | TernaryIf (predicate, texpr, fexpr) ->
        TernaryIf (mod_expr predicate, mod_expr texpr, mod_expr fexpr)
    | Indexed (idx_expr, indexed) ->
        let query_index = mod_index mod_expr in
        Indexed (mod_expr idx_expr, List.map ~f:query_index indexed)
    | Var (_ : string) | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string))
      ->
        pattern
    | EAnd (lhs, rhs) -> EAnd (mod_expr lhs, mod_expr rhs)
    | EOr (lhs, rhs) -> EOr (mod_expr lhs, mod_expr rhs)
  in
  {expr with pattern= new_pattern}

let rec demote_sizedtype_mem st =
  match st with
  | (SizedType.SInt | SReal) as ret -> ret
  | SVector (SoA, dim) -> SVector (AoS, dim)
  | SRowVector (SoA, dim) -> SRowVector (AoS, dim)
  | SMatrix (SoA, dim1, dim2) -> SMatrix (AoS, dim1, dim2)
  | SArray (inner_type, dim) -> SArray (demote_sizedtype_mem inner_type, dim)
  | _ -> st

let rec promote_sizedtype_mem st =
  match st with
  | (SizedType.SInt | SReal) as ret -> ret
  | SVector (AoS, dim) -> SVector (SoA, dim)
  | SRowVector (AoS, dim) -> SRowVector (SoA, dim)
  | SMatrix (AoS, dim1, dim2) -> SMatrix (SoA, dim1, dim2)
  | SArray (inner_type, dim) -> SArray (promote_sizedtype_mem inner_type, dim)
  | _ -> st

(**
 * Internal to the module, used when looking recursivly
 *  in statment patterns that have hold statements
 *)
let modify_soa_stmts (var_name : string Set.Poly.t) pattern_fn
    (Stmt.Fixed.({pattern; _}) as stmt) =
  {stmt with pattern= pattern_fn pattern var_name}

(**
 * Demote statements in the MIR so that they go from Struct of Arrays (SoA) 
 *  to Array of Structs (AoS)
 * @param pattern The statement to modify 
 * @param var_name The name of the variable we are searching for.
 *)
let mod_soa_stmt_pattern
    (pattern : ('a Fixed.t, ('a, 'b) Stmt.Fixed.t) Stmt.Fixed.Pattern.t)
    (var_name : string Core_kernel.Set.Poly.t) =
  let mod_expr = modify_soa_exprs var_name in
  let find_name = query_aos_set_names var_name in
  match pattern with
  | Decl {decl_adtype; decl_id; decl_type= Type.Sized sized_type}
    when Set.exists ~f:(fun x -> x = decl_id) var_name ->
      Stmt.Fixed.Pattern.Decl
        { decl_adtype
        ; decl_id
        ; decl_type= Type.Sized (promote_sizedtype_mem sized_type) }
  | Decl {decl_adtype; decl_id; decl_type= Type.Sized sized_type}
    when not (Set.exists ~f:(fun x -> x = decl_id) var_name) ->
      Stmt.Fixed.Pattern.Decl
        { decl_adtype
        ; decl_id
        ; decl_type= Type.Sized (demote_sizedtype_mem sized_type) }
  | Decl _ -> pattern
  | NRFunApp (kind, (exprs : 'a Expr.Fixed.t list)) ->
      let modify_funs kind =
        match kind with
        | Fun_kind.StanLib (name, sfx, Common.Helpers.AoS) as func -> (
          match List.exists ~f:find_name exprs with
          | true -> Fun_kind.StanLib (name, sfx, Common.Helpers.SoA)
          | false -> func )
        | _ -> kind
      in
      NRFunApp (modify_funs kind, exprs)
  | Assignment
      ( ((name : string), (ut : UnsizedType.t), lhs)
      , ( { pattern=
              FunApp (CompilerInternal (FnReadParam (constrain_op, AoS)), args); _
          } as rhs ) ) as orig_pattern ->
      if
        Set.Poly.exists ~f:(fun x -> x = name) var_name
        && not (UnsizedType.contains_eigen_type ut)
      then
        Assignment
          ( (name, ut, lhs)
          , { rhs with
              pattern=
                FunApp
                  (CompilerInternal (FnReadParam (constrain_op, SoA)), args) }
          )
      else orig_pattern
  | Assignment (((name : string), (ut : UnsizedType.t), lhs), rhs) ->
      let query_index = mod_index mod_expr in
      Assignment ((name, ut, List.map ~f:query_index lhs), mod_expr rhs)
  | Skip | Break | Continue | Return _ | TargetPE _ | IfElse _ | Block _
   |SList _ | For _ | Profile _ | While _ ->
      pattern

(* Look through an expression and find the overall type and adlevel*)
let find_args Expr.Fixed.({meta= Expr.Typed.Meta.({type_; adlevel; _}); _}) =
  (adlevel, type_)

let query_expr_funs expr_query success_lst kind exprs =
  let query_expr = expr_query success_lst in
  let query_name = query_aos_names success_lst in
  let get_names = get_aos_set_names in
  let expr_names = Set.Poly.union_list (List.map ~f:get_names exprs) in
  match kind with
  | Fun_kind.StanLib ((name : string), (_ : bool Fun_kind.suffix), _) -> (
      let does_name_exist = List.exists ~f:query_name exprs in
      match does_name_exist with
      | false -> success_lst
      | true -> (
        match name with
        | x when Stan_math_signatures.is_reduce_sum_fn x ->
            Set.Poly.diff expr_names success_lst
        | x when Stan_math_signatures.is_variadic_ode_fn x ->
            Set.Poly.diff expr_names success_lst
        | x when x = "reduce_sum" -> Set.Poly.diff expr_names success_lst
        | _ ->
            let check_fun_support =
              Stan_math_signatures.query_stan_math_mem_pattern_support name
                (List.map ~f:find_args exprs)
            in
            if check_fun_support then
              Set.Poly.union_list (List.map ~f:query_expr exprs)
            else Set.Poly.diff expr_names success_lst ) )
  | CompilerInternal _ -> success_lst
  | UserDefined _ -> Set.Poly.diff expr_names success_lst

(* Look through an expression to see whether it needs modified from
 * SoA to AoS.
 * TODO: The logic on when to return true/false is wrong.
 * I really want to move from returning true/false to return SoA/AoS
 * which should be a lot easier to read.
 *  I think we want to use this in an "is any" style context
 *
 * Logic for deciding if the object can use SoA is:
 * If we find a FunApp
 *  - If the FunApp (StanLib _) is an SoA, check if the object's name exists 
 *     in the expressions and whether that signature supports 
 *     SoA.
 *  - If we find a FunApp (StanLib _) that is not SoA or is UserDefined,
 *    check that the name, chat that the object name is not used in
 *    the expressions for the 
 * For Assignments
 * If the assignee's name is in the list of known failures 
 *)
let rec query_aos_exprs (success_lst : string Set.Poly.t)
    Expr.Fixed.({pattern; _}) =
  let query_expr = query_aos_exprs success_lst in
  match pattern with
  | FunApp (kind, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
      query_expr_funs query_aos_exprs success_lst kind exprs
  | TernaryIf (predicate, texpr, fexpr) ->
      Set.Poly.union_list
        [query_expr predicate; query_expr texpr; query_expr fexpr]
  | Indexed (expr, indexed) ->
      let query_index = search_index success_lst query_expr in
      Set.Poly.union_list
        [query_expr expr; Set.Poly.union_list (List.map ~f:query_index indexed)]
  | Var (_ : string) | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) ->
      success_lst
  | EAnd (lhs, rhs) | EOr (lhs, rhs) ->
      Set.Poly.union_list [query_expr lhs; query_expr rhs]

(* Look through a statement to see whether it needs modified from
 * SoA to AoS. Returns true if object needs changed from SoA to AoS.
 *
 * Rules:
 * 1. Decl is data only or contains and int or real type, return true
 * 2. StanLib functions return true if any of
 *   - The name exists in the exprs of the function
 *   - The function does not support SoA
 *   - The exprs satisfies the query_aos_exprs checks
 * 3. (TODO: UserDefined)
 *  - I'm not sure how to do these yet
 *  - For these we need to lookup the body of the user defined function,
 *   check all these rules for the UDF, and if it passes tag it as SoA,
 *   and if not tag it as AoS. But then we run into this problem where
 *  we need to have multiple function definitions when some input types can
 *  or cannot be AoS or SoA.
 *  For now I think it's better to just check if the variable name
 *  is in the list of expressions to the user defined function and fail
 *  the variable if we see it enter a UDF.
 * 4. Assignment return true if
 *     - The object being assigned to is in the list of known failures and
 *    - any of
 *     - The expression query from the indexed expression returns true 
 *     - The expression query from the rhs of the assignment returns true
 *   -  I think I also need to return true if the assigned to object is
 *      in the list of known failures the variable exists 
 *      on the right hand side or in the indexed type?
 *
 * 4. (TODO: For loops)
 *  Single indexing is fine outside of loops, but in loops we need to return true
 *
 * All other statements simply recurse into their lists of expressions 
 *  or statements repeating the checks from above.
 *)
let rec query_aos_stmts (success_lst : string Set.Poly.t)
    (stmt_map : (int, Stmt.Located.Non_recursive.t) Core_kernel.Map.Poly.t)
    Stmt.Located.Non_recursive.({pattern; _}) =
  let query_expr = query_aos_exprs success_lst in
  let query_stmt = query_aos_stmts success_lst stmt_map in
  let get_key key = Map.find_exn stmt_map key in
  let find_pattern (pattern : (Expr.Typed.t, cf_state) Stmt.Fixed.Pattern.t) =
    match pattern with
    | NRFunApp (kind, (exprs : Expr.Typed.Meta.t Expr.Fixed.t list)) ->
        query_expr_funs query_aos_exprs success_lst kind exprs
    | Assignment (((assign_name : string), (_ : UnsizedType.t), lhs), rhs) ->
        let query_index = search_index success_lst query_expr in
        let check_name item = assign_name = item in
        let is_good_assign = Set.Poly.exists ~f:check_name success_lst in
        if is_good_assign then
          Set.Poly.inter
            (Set.Poly.union_list (List.map ~f:query_index lhs))
            (query_expr rhs)
        else
          let get_names = get_aos_set_names in
          let expr_names = get_names rhs in
          Set.Poly.diff expr_names success_lst
    | IfElse (predicate, (_ : label), (_ : label option)) ->
        query_expr predicate
    | For {lower; upper; body; _} ->
        Set.Poly.inter
          (Set.Poly.inter (query_expr lower) (query_expr upper))
          (query_stmt (get_key body))
    | TargetPE expr -> query_expr expr
    | Return optional_expr -> (
      match optional_expr with
      | Some expr -> query_expr expr
      | None -> success_lst )
    | Profile _ -> success_lst
    | Decl _ -> success_lst
    | Block (_ : label list) -> success_lst
    | SList (_ : label list) -> success_lst
    | Skip | Break | Continue -> success_lst
    | While (predicate, body) ->
        Set.Poly.inter (query_expr predicate) (query_stmt (get_key body))
  in
  find_pattern pattern
