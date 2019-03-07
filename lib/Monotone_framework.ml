(** The common elements of a monotone framework *)

open Core_kernel
open Monotone_framework_sigs

(* TODO: write instance of FLOWGRAPH for Stan flowgraph of Stan MIR
         write instance of TRANSFER_FUNCTION for available expressions
                                                 reaching definitions
                                                 live variables
                                                 constant propagation
                                                 very busy expressions (anticipated expressions)
                                                 used expressions
                                                 postponable expressions *)

(** Reverse flowgraphs to be used for reverse analyses.
    Observe that this respects the invariants listed for a FLOWGRAPH *)
module Reverse (F : FLOWGRAPH) : FLOWGRAPH = struct
  type labels = F.labels
  type t = labels

  let compare = F.compare
  let hash = F.hash
  let sexp_of_t = F.sexp_of_t
  let initials = Set.of_map_keys (Map.filter F.successors ~f:Set.is_empty)

  let successors =
    Map.fold F.successors
      ~init:(Map.map F.successors ~f:(fun _ -> Set.Poly.empty))
      ~f:(fun ~key:old_pred ~data:old_succs accum ->
        Set.fold old_succs ~init:accum ~f:(fun accum old_succ ->
            Map.set accum ~key:old_succ
              ~data:(Set.add (Map.find_exn accum old_succ) old_pred) ) )
end

module Powerset_lattice (S : INITIALTYPE) : LATTICE = struct
  type properties = S.vals Set.Poly.t

  let bottom = Set.Poly.empty
  let lub s1 s2 = Set.Poly.union s1 s2
  let leq s1 s2 = Set.Poly.is_subset s1 ~of_:s2
  let initial = S.initial
end

module Dual_powerset_lattice (S : INITIALTOTALTYPE) : LATTICE = struct
  type properties = S.vals Set.Poly.t

  let bottom = S.total
  let lub s1 s2 = Set.Poly.inter s1 s2
  let leq s1 s2 = Set.Poly.is_subset s2 ~of_:s1
  let initial = S.initial
end

module New_bot (L : LATTICE) : LATTICE = struct
  type properties = L.properties option

  let bottom = None

  let lub = function
    | Some s1 -> ( function Some s2 -> Some (L.lub s1 s2) | None -> Some s1 )
    | None -> fun x -> x

  let leq = function
    | Some s1 -> ( function Some s2 -> L.leq s1 s2 | None -> false )
    | None -> fun _ -> true

  let initial = Some L.initial
end

module Dual_partial_function_lattice (Dom : INITIALTYPE) (Codom : TYPE) :
  LATTICE = struct
  type properties = (Dom.vals, Codom.vals) Map.Poly.t

  let bottom = Errors.fatal_error ()

  let lub s1 s2 =
    let f ~key ~data = Map.find s2 key = Some data in
    Map.filteri ~f s1

  let leq s1 s2 =
    Set.for_all Dom.initial ~f:(fun k ->
        match (Map.find s1 k, Map.find s2 k) with
        | Some x, Some y -> x = y
        | Some _, None | None, None -> true
        | None, Some _ -> false )

  let initial = Map.Poly.empty
end

(* To use for constant propagation analysis *)
module Dual_partial_function_lattice_with_bot
    (Dom : INITIALTYPE)
    (Codom : TYPE) : LATTICE =
  New_bot (Dual_partial_function_lattice (Dom) (Codom))

(* To use for very busy expressions (anticipated expressions)
              available expressions
              postponable expresions
   analyses *)
module Dual_powerset_lattice_empty_initial (T : TOTALTYPE) : LATTICE =
Dual_powerset_lattice (struct
  type vals = T.vals

  let initial = Set.Poly.empty
  let total = T.total
end)

(* To use for used expressions
              live variables
   analyses *)
module Powerset_lattice_empty_initial (T : TYPE) : LATTICE =
Powerset_lattice (struct
  type vals = T.vals

  let initial = Set.Poly.empty
end)

(* To use for reaching definitions analysis *)
module Reaching_definitions_lattice (Variables : INITIALTYPE) (Labels : TYPE) :
  LATTICE = Powerset_lattice (struct
  type vals = Variables.vals * Labels.vals option

  let initial = Set.Poly.map ~f:(fun x -> (x, None)) Variables.initial
end)

(* TODO: this is temporary until Ryan's code to get the real flow graph is
   merged *)

let flowgraph_to_mir : (int, Mir.stmt_loc) Map.Poly.t = Map.Poly.empty

module Constant_propagation_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = (string, Mir.expr) Map.Poly.t option

  let transfer_function l p =
    match p with
    | None -> None
    | Some m ->
        let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
        Some
          ( match mir_node with
          (* TODO: we are currently only propagating constants for scalars.
             We could do the same for matrix and array expressions if we wanted. *)
          | Mir.Assignment (Var s, Mir.Lit (t, v)) ->
              Map.set m ~key:s ~data:(Mir.Lit (t, v))
          | Mir.Decl {decl_id= s; _} | Mir.Assignment (Var s, _) ->
              Map.remove m s
          | Mir.Assignment (_, _)
           |Mir.TargetPE _
           |Mir.NRFunApp (_, _)
           |Mir.Check _ | Mir.Break | Mir.Continue | Mir.Return _ | Mir.Skip
           |Mir.IfElse (_, _, _)
           |Mir.While (_, _)
           |Mir.For _ | Mir.Block _ | Mir.SList _ | Mir.FunDef _ ->
              m )
end

let transfer_gen_kill p gen kill = Set.union gen (Set.diff p kill)

module Reaching_definitions_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = (string * labels option) Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (Var x, _)
       |Mir.Assignment (Indexed (Var x, _), _)
       |Mir.FunDef {fdname= x; _} ->
          Set.Poly.singleton (x, Some l)
      | Mir.Assignment (_, _) -> Errors.fatal_error ()
      | Mir.TargetPE _ -> Set.Poly.singleton ("target", Some l)
      | Mir.NRFunApp (s, _) when String.suffix s 3 = "_lp" ->
          Set.Poly.singleton ("target", Some l)
      | Mir.NRFunApp (_, _)
       |Mir.Check _ | Mir.Break | Mir.Continue | Mir.Return _ | Mir.Skip
       |Mir.IfElse (_, _, _)
       |Mir.While (_, _)
       |Mir.For _ | Mir.Block _ | Mir.SList _ | Mir.Decl _ ->
          Set.Poly.empty
    in
    let kill =
      match mir_node with
      | Mir.Decl {decl_id= x; _}
       |Mir.Assignment (Var x, _)
       |Mir.Assignment (Indexed (Var x, _), _)
       |Mir.FunDef {fdname= x; _} ->
          Set.filter p ~f:(fun (y, _) -> y = x)
      | Mir.Assignment (_, _) -> Errors.fatal_error ()
      | Mir.TargetPE _ -> Set.filter p ~f:(fun (y, _) -> y = "target")
      | Mir.NRFunApp (s, _) when String.suffix s 3 = "_lp" ->
          Set.filter p ~f:(fun (y, _) -> y = "target")
      | Mir.NRFunApp (_, _)
       |Mir.Check _ | Mir.Break | Mir.Continue | Mir.Return _ | Mir.Skip
       |Mir.IfElse (_, _, _)
       |Mir.While (_, _)
       |Mir.For _ | Mir.Block _ | Mir.SList _ ->
          Set.Poly.empty
    in
    transfer_gen_kill p gen kill
end

module Live_variables_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = string Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    let kill =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    transfer_gen_kill p gen kill
end

module Anticipated_expressions_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = Mir.expr Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    let kill =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    (* NOTE: this is note quite the usual gen kill pattern *)
    Set.union gen (Set.diff p kill)
end

(* NOTE: we want to implement lazy code motion. Aho describes a slightly
   different available expression pass for that that uses the anticipated
   expression pass. *)
module Available_expressions_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = Mir.expr Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    let kill =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    transfer_gen_kill p gen kill
end

module Postponable_expressions_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = Mir.expr Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    let kill =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    transfer_gen_kill p gen kill
end

module Used_expressions_transfer : TRANSFER_FUNCTION = struct
  type labels = int
  type properties = Mir.expr Set.Poly.t

  let transfer_function l p =
    let mir_node = (Map.find_exn flowgraph_to_mir l).stmt in
    let gen =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    let kill =
      match mir_node with
      | Mir.Assignment (_, _) -> failwith "<case>"
      | Mir.TargetPE _ -> failwith "<case>"
      | Mir.NRFunApp (_, _) -> failwith "<case>"
      | Mir.Check _ -> failwith "<case>"
      | Mir.Break -> failwith "<case>"
      | Mir.Continue -> failwith "<case>"
      | Mir.Return _ -> failwith "<case>"
      | Mir.Skip -> failwith "<case>"
      | Mir.IfElse (_, _, _) -> failwith "<case>"
      | Mir.While (_, _) -> failwith "<case>"
      | Mir.For _ -> failwith "<case>"
      | Mir.Block _ -> failwith "<case>"
      | Mir.SList _ -> failwith "<case>"
      | Mir.Decl _ -> failwith "<case>"
      | Mir.FunDef _ -> failwith "<case>"
    in
    transfer_gen_kill p gen kill
end

module Monotone_framework : MONOTONE_FRAMEWORK =
functor
  (F : FLOWGRAPH)
  (L : LATTICE)
  (T :
     TRANSFER_FUNCTION
     with type labels = F.labels
      and type properties = L.properties)
  ->
  struct
    let mfp () =
      (* STEP 1: initialize data structures *)
      let workstack = Stack.create () in
      (* TODO: does the order matter a lot for efficiency here? *)
      let _ =
        Map.iteri F.successors ~f:(fun ~key ~data ->
            Set.iter data ~f:(fun succ -> Stack.push workstack (key, succ)) )
      in
      let analysis_in = Hashtbl.create (module F) in
      let nodes = Set.of_map_keys F.successors in
      let _ =
        Set.iter
          ~f:(fun l ->
            Hashtbl.add_exn analysis_in ~key:l
              ~data:(if Set.mem F.initials l then L.initial else L.bottom) )
          nodes
      in
      (* STEP 2: iterate *)
      let _ =
        while Stack.length workstack <> 0 do
          let l, l' = Stack.pop_exn workstack in
          let old_analysis_out_l' = Hashtbl.find_exn analysis_in l' in
          let new_analysis_out_l' =
            T.transfer_function l (Hashtbl.find_exn analysis_in l)
          in
          let _ =
            if not (L.leq new_analysis_out_l' old_analysis_out_l') then
              Hashtbl.set analysis_in ~key:l'
                ~data:(L.lub old_analysis_out_l' new_analysis_out_l')
          in
          Set.iter (Map.find_exn F.successors l') ~f:(fun l'' ->
              Stack.push workstack (l', l'') )
        done
      in
      (* STEP 3: present final results *)
      let analysis_out =
        Set.fold ~init:Map.Poly.empty
          ~f:(fun accum l ->
            Map.add_exn accum ~key:l
              ~data:(T.transfer_function l (Hashtbl.find_exn analysis_in l)) )
          nodes
      in
      (Map.Poly.of_hashtbl_exn analysis_in, analysis_out)
  end