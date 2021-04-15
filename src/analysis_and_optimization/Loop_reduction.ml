(* A partial evaluator for use in static analysis and optimization *)

open Core_kernel
(*open Mir_utils*)
open Middle

let preserve_stability = false

let is_int i Expr.Fixed.({pattern; _}) =
  let nums = List.map ~f:(fun s -> string_of_int i ^ s) [""; "."; ".0"] in
  match pattern with
  | (Lit (Int, i) | Lit (Real, i)) when List.mem nums i ~equal:String.equal ->
      true
  | _ -> false

let apply_prefix_operator_int (op : string) i =
  Expr.Fixed.Pattern.Lit
    ( Int
    , Int.to_string
        ( match op with
        | "PPlus__" -> i
        | "PMinus__" -> -i
        | "PNot__" -> if i = 0 then 1 else 0
        | s -> raise_s [%sexp (s : string)] ) )

let apply_prefix_operator_real (op : string) i =
  Expr.Fixed.Pattern.Lit
    ( Real
    , Float.to_string
        ( match op with
        | "PPlus__" -> i
        | "PMinus__" -> -.i
        | s -> raise_s [%sexp (s : string)] ) )

let apply_operator_int (op : string) i1 i2 =
  Expr.Fixed.Pattern.Lit
    ( Int
    , Int.to_string
        ( match op with
        | "Plus__" -> i1 + i2
        | "Minus__" -> i1 - i2
        | "Times__" -> i1 * i2
        | "Divide__" -> i1 / i2
        | "IntDivide__" -> i1 / i2
        | "Modulo__" -> i1 % i2
        | "Equals__" -> Bool.to_int (i1 = i2)
        | "NEquals__" -> Bool.to_int (i1 <> i2)
        | "Less__" -> Bool.to_int (i1 < i2)
        | "Leq__" -> Bool.to_int (i1 <= i2)
        | "Greater__" -> Bool.to_int (i1 > i2)
        | "Geq__" -> Bool.to_int (i1 >= i2)
        | s -> raise_s [%sexp (s : string)] ) )

let apply_arithmetic_operator_real (op : string) r1 r2 =
  Expr.Fixed.Pattern.Lit
    ( Real
    , Float.to_string
        ( match op with
        | "Plus__" -> r1 +. r2
        | "Minus__" -> r1 -. r2
        | "Times__" -> r1 *. r2
        | "Divide__" -> r1 /. r2
        | s -> raise_s [%sexp (s : string)] ) )

let apply_logical_operator_real (op : string) r1 r2 =
  Expr.Fixed.Pattern.Lit
    ( Int
    , Int.to_string
        ( match op with
        | "Equals__" -> Bool.to_int (r1 = r2)
        | "NEquals__" -> Bool.to_int (r1 <> r2)
        | "Less__" -> Bool.to_int (r1 < r2)
        | "Leq__" -> Bool.to_int (r1 <= r2)
        | "Greater__" -> Bool.to_int (r1 > r2)
        | "Geq__" -> Bool.to_int (r1 >= r2)
        | s -> raise_s [%sexp (s : string)] ) )

let is_multi_index = function
  | Index.MultiIndex _ | Upfrom _ | Between _ | All -> true
  | Single _ -> false

let is_single_index loopvar a =
match a with
| Index.MultiIndex _ | Upfrom _ | Between _ | All -> false
| Single Expr.Fixed.{pattern= Var s; _} when s = loopvar ->  true
| Single _ ->  false


let get_lvalue_idx (loopvar, (_, _, c)) = 
  let loopvar_checker = is_single_index loopvar in 
  if List.for_all ~f:loopvar_checker c then 
  true 
  else 
  false

let is_single_loopvar_index (loopvar, idx_lvalue) = 
    match get_lvalue_idx (loopvar, idx_lvalue) with
    | _ -> true

  
    (** Query function expressions in expressions returning back a list of optionals 
 *    with each Some element holding the queried function types.
 * @param select A functor taking in a tuple of the same types as 
 *  those in `FunApp` and returning a subset of the `FunApp`'s types.
 * @param where A functor that accepts a tuple returned by select
 *  and returns either true or false.
 *  This is used to decide if a function's subsetted tuple should be returned.
 * @param pattern A pattern of fixed expressions to recurse over.

 let rec query_expr_functions select (where : 'a -> bool)
 Expr.Fixed.({pattern; _}) =
let query_expr = query_expr_functions select where in
match pattern with
| FunApp (kind, exprs) -> (
   let subset = select (kind, exprs) in
   match where subset with
   | true -> List.concat [[Some subset]; List.concat_map ~f:query_expr exprs]
   | false -> List.concat_map ~f:query_expr exprs )
| TernaryIf (predicate, texpr, fexpr) ->
   List.concat_map ~f:query_expr [predicate; texpr; fexpr]
| EAnd (lhs, rhs) -> List.concat_map ~f:query_expr [lhs; rhs]
| EOr (lhs, rhs) -> List.concat_map ~f:query_expr [lhs; rhs]
| Indexed (expr, indexed) ->
   let query_index ind =
     match ind with
     | Index.All -> [None]
     | Single index_expr -> query_expr index_expr
     | Upfrom index_expr -> query_expr index_expr
     | Between (expr_top, expr_bottom) ->
         List.concat_map ~f:query_expr [expr_top; expr_bottom]
     | MultiIndex exprs -> query_expr exprs
   in
   List.concat [query_expr expr; List.concat_map ~f:query_index indexed]
(*Vars and Literal types can't hold rngs*)
| Var (_ : string) | Lit ((_ : Expr.Fixed.Pattern.litType), (_ : string)) ->
   [None]
 *)

let really_zip_loop (loopvar, _, _, Stmt.Fixed.({pattern; meta}) ) =
  match pattern with 
  | Assignment (a, _) -> 
  let a_loopvar_idx = is_single_loopvar_index (loopvar, a) in
  let all_conditionals_satisfied = a_loopvar_idx in
  if all_conditionals_satisfied then 
  Stmt.Fixed.({pattern; meta})
  else 
  Stmt.Fixed.({pattern; meta})
  | _ -> Stmt.Fixed.({pattern; meta})


let zip_for_loop (loopvar, lower, upper, Stmt.Fixed.({pattern; meta})) = 
    match pattern with
    | Block [a] -> 
      Stmt.Fixed.({pattern=Block [really_zip_loop (loopvar, lower, upper, a)]; meta})
    | _ -> Stmt.Fixed.({pattern; meta})
(** Query function expressions in statements returning back a list
 *   of optionals with the the elements of the list holding the 
 *   selected subset of function arguments.
 *   For an example of this function see `pp_rng_in_td`.
 * @param select A functor taking in a tuple of the same types as 
 *  those in `FunApp` and returning a subset of the `FunApp`'s types.
 * @param where A functor that accepts a tuple returned by select
 *   returning true or false. This is used to decide if a function's
 *   subsetted tuple should be returned.
 * @param pattern A pattern of fixed statements to recurse over.
 *)
let rec squish_stmt_loops stmt =
  let inner_query Stmt.Fixed.({pattern; meta}) =
    (match pattern with
    | Assignment _ -> stmt
    | TargetPE _ -> stmt
    | NRFunApp _ -> stmt
    | Break | Continue -> stmt
    | Return _ -> stmt
    | Skip -> stmt
    | IfElse (predicate, true_stmt, op_false_stmt) -> 
      let false_stmt = 
        (match op_false_stmt with 
        | Some stmt -> 
          let ahh = squish_stmt_loops stmt in Some ahh  
        | None -> None) in
      Stmt.Fixed.({pattern=IfElse (predicate, squish_stmt_loops true_stmt, false_stmt); meta=meta})
    | While _ -> stmt
    | For {loopvar; lower; upper; body} ->
      let new_body = zip_for_loop (loopvar, lower, upper, body) in
      Stmt.Fixed.({pattern=For {loopvar; lower; upper; body=new_body}; meta=meta})
    | Profile _ -> stmt
    | Block stmts -> 
      let new_stmts = List.map ~f:squish_stmt_loops stmts in
      Stmt.Fixed.({pattern= Block new_stmts; meta=meta})
    | SList stmts -> 
      let new_stmts = List.map ~f:squish_stmt_loops stmts in
      Stmt.Fixed.({pattern= SList new_stmts; meta=meta})
    | Decl {decl_adtype; decl_id; decl_type} -> 
      Stmt.Fixed.({pattern=Decl {decl_adtype; decl_id; decl_type}; meta=meta}))
in 
  inner_query stmt

let eval_prog :
  (Expr.Typed.t, Stmt.Located.t) Program.t
-> (Expr.Typed.t, Stmt.Located.t) Program.t =
Program.map Fn.id squish_stmt_loops

