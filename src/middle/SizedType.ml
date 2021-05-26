open Core_kernel
open Common

type 'a t =
  | SInt
  | SReal
  | SVector of Common.Helpers.mem_pattern * 'a
  | SRowVector of Common.Helpers.mem_pattern * 'a
  | SMatrix of Common.Helpers.mem_pattern * 'a * 'a
  | SArray of 'a t * 'a
[@@deriving sexp, compare, map, hash, fold]

let rec pp pp_e ppf = function
  | SInt -> Fmt.string ppf "int"
  | SReal -> Fmt.string ppf "real"
  | SVector (_, expr) -> Fmt.pf ppf {|vector%a|} (Fmt.brackets pp_e) expr
  | SRowVector (_, expr) ->
      Fmt.pf ppf {|row_vector%a|} (Fmt.brackets pp_e) expr
  | SMatrix (_, d1_expr, d2_expr) ->
      Fmt.pf ppf {|matrix%a|}
        Fmt.(pair ~sep:comma pp_e pp_e |> brackets)
        (d1_expr, d2_expr)
  | SArray (st, expr) ->
      Fmt.pf ppf {|array%a|}
        Fmt.(pair ~sep:comma (fun ppf st -> pp pp_e ppf st) pp_e |> brackets)
        (st, expr)

let collect_exprs st =
  let rec aux accu = function
    | SInt | SReal -> List.rev accu
    | SVector (_, expr) | SRowVector (_, expr) -> List.rev @@ (expr :: accu)
    | SMatrix (_, expr1, expr2) -> List.rev @@ (expr1 :: expr2 :: accu)
    | SArray (inner, expr) -> aux (expr :: accu) inner
  in
  aux [] st

let rec to_unsized = function
  | SInt -> UnsizedType.UInt
  | SReal -> UReal
  | SVector _ -> UVector
  | SRowVector _ -> URowVector
  | SMatrix _ -> UMatrix
  | SArray (t, _) -> UArray (to_unsized t)

let rec associate ?init:(assocs = Label.Int_label.Map.empty) = function
  | SInt | SReal -> assocs
  | SVector (_, expr) | SRowVector (_, expr) ->
      Expr.Labelled.associate ~init:assocs expr
  | SMatrix (_, expr1, expr2) ->
      Expr.Labelled.(associate ~init:(associate ~init:assocs expr1) expr2)
  | SArray (st, e) ->
      associate ~init:(Expr.Labelled.associate ~init:assocs e) st

let is_scalar = function SInt | SReal -> true | _ -> false
let rec inner_type = function SArray (t, _) -> inner_type t | t -> t

let rec contains_soa st =
  match st with
  | SInt -> false
  | SReal -> false
  | SVector (SoA, _) | SRowVector (SoA, _) | SMatrix (SoA, _, _) -> true
  | SVector (AoS, _) | SRowVector (AoS, _) | SMatrix (AoS, _, _) -> false
  | SArray (t, _) -> contains_soa t

let rec get_soa st =
  match st with
  | SInt -> Common.Helpers.AoS
  | SReal -> AoS
  | SVector (SoA, _) | SRowVector (SoA, _) | SMatrix (SoA, _, _) -> SoA
  | SVector (AoS, _) | SRowVector (AoS, _) | SMatrix (AoS, _, _) -> AoS
  | SArray (t, _) -> get_soa t

let rec dims_of st =
  match st with
  | SArray (t, _) -> dims_of t
  | SMatrix (_, dim1, dim2) -> [dim1; dim2]
  | SRowVector (_, dim) | SVector (_, dim) -> [dim]
  | SInt | SReal -> []

let rec get_dims st =
  match st with
  | SInt | SReal -> []
  | SVector (_, dim) | SRowVector (_, dim) -> [dim]
  | SMatrix (_, dim1, dim2) -> [dim1; dim2]
  | SArray (t, dim) -> dim :: get_dims t

let%expect_test "dims" =
  let open Fmt in
  strf "@[%a@]" (list ~sep:comma string)
    (get_dims (SArray (SMatrix (SoA, "x", "y"), "z")))
  |> print_endline ;
  [%expect {| z, x, y |}]
