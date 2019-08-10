open Core_kernel
open Common
open State
open Helpers

(** Fixed-point of statements *)
module Fixed = struct
  module First = Expr.Fixed

  module Pattern = struct
    type ('a, 'b) t = ('a, 'b) Mir_pattern.statement =
      | Assignment of (string * 'a Expr.index list) * 'a
      | TargetPE of 'a
      | NRFunApp of Fun_kind.t * string * 'a list
      | Break
      | Continue
      | Return of 'a option
      | Skip
      | IfElse of 'a * 'b * 'b option
      | While of 'a * 'b
      | For of {loopvar: string; lower: 'a; upper: 'a; body: 'b}
      | Block of 'b list
      | SList of 'b list
      | Decl of
          { decl_adtype: UnsizedType.autodifftype
          ; decl_id: string
          ; decl_type: 'a Type.t }
    [@@deriving sexp, hash, map, fold, compare]




    let pp pp_e pp_s ppf = function
      | Assignment ((assignee, idcs), rhs) ->
          Fmt.pf ppf {|@[<h>%a =@ %a;@]|} (Expr.pp_indexed pp_e) (assignee, idcs) pp_e
            rhs
      | TargetPE expr ->
          Fmt.pf ppf {|@[<h>%a +=@ %a;@]|} pp_keyword "target" pp_e expr
      | NRFunApp (_, name, args) ->
          Fmt.pf ppf {|@[%s%a;@]|} name Fmt.(list pp_e ~sep:comma |> parens) args
      | Break -> pp_keyword ppf "break;"
      | Continue -> pp_keyword ppf "continue;"
      | Skip -> pp_keyword ppf ";"
      | Return (Some expr) -> Fmt.pf ppf {|%a %a;|} pp_keyword "return" pp_e expr
      | Return _ -> pp_keyword ppf "return;"
      | IfElse (pred, s_true, Some s_false) ->
          Fmt.pf ppf {|%a(%a) %a %a %a|} pp_builtin_syntax "if" pp_e pred pp_s
            s_true pp_builtin_syntax "else" pp_s s_false
      | IfElse (pred, s_true, _) ->
          Fmt.pf ppf {|%a(%a) %a|} pp_builtin_syntax "if" pp_e pred pp_s s_true
      | While (pred, stmt) ->
          Fmt.pf ppf {|%a(%a) %a|} pp_builtin_syntax "while" pp_e pred pp_s stmt
      | For {loopvar; lower; upper; body} ->
          Fmt.pf ppf {|%a(%s in %a:%a) %a|} pp_builtin_syntax "for" loopvar pp_e
            lower pp_e upper pp_s body
      | Block stmts ->
          Fmt.pf ppf {|{@;<1 2>@[<v>%a@]@;}|} Fmt.(list pp_s ~sep:Fmt.cut) stmts
      | SList stmts -> Fmt.(list pp_s ~sep:Fmt.cut |> vbox) ppf stmts
      | Decl {decl_adtype; decl_id; decl_type} ->
          Fmt.pf ppf {|%a%a %s;|} UnsizedType.pp_autodifftype decl_adtype
            (Type.pp pp_e)
            decl_type decl_id


    include Bifoldable.Make (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let fold = fold
    end)

    module Make_traversable = Mir_pattern.Make_traversable_statement
    module Make_traversable2 = Mir_pattern.Make_traversable_statement2
  end

  include Fix.Make2 (First) (Pattern)
  module Traversable_state = Make_traversable2 (Cps.State)
  module Traversable_state_r = Make_traversable2 (Right.Cps.State)

  let map_accum_left ~f ~g ~init x =
    Cps.State.(
      Traversable_state.traverse x
        ~f:(fun a -> state @@ Fn.flip f a)
        ~g:(fun a -> state @@ Fn.flip g a)
      |> run_state ~init)

  let map_accum_right ~f ~g ~init x =
    Right.Cps.State.(
      Traversable_state_r.traverse x
        ~f:(fun a -> state @@ Fn.flip f a)
        ~g:(fun a -> state @@ Fn.flip g a)
      |> run_state ~init)
end

(** Statements with no meta-data *)
module NoMeta = struct
  module Meta = struct
    type t = unit [@@deriving compare, sexp, hash]

    let pp _ _ = ()
  end

  include Specialized.Make2 (Fixed) (Expr.NoMeta) (Meta)

  let remove_meta x = Fixed.map (fun _ -> ()) (fun _ -> ()) x
end

(** Statements with location information and types for contained expressions *)
module Located = struct
  module Meta = struct
    type t = (Location_span.t sexp_opaque[@compare.ignore])
    [@@deriving compare, sexp, hash]

    let pp _ _ = ()
  end

  include Specialized.Make2 (Fixed) (Expr.Typed) (Meta)

  let loc_of x = Fixed.meta x
end

(** Statements with location information, labels and types for contained 
expressions 
*)
module Labelled = struct
  module Meta = struct
    type t =
      { loc: Location_span.t sexp_opaque [@compare.ignore]
      ; label: Int_label.t [@compare.ignore] }
    [@@deriving compare, create, sexp, hash]

    let label {label; _} = label
    let loc {loc; _} = loc
    let pp _ _ = ()
  end

  include Specialized.Make2 (Fixed) (Expr.Labelled) (Meta)

  let label_of x = Meta.label @@ Fixed.meta x
  let loc_of x = Meta.loc @@ Fixed.meta x

  module Traversable_state = Fixed.Make_traversable2 (State)

  let label ?(init = Int_label.init) (stmt : Located.t) : t  =
    let f label Expr.Typed.Meta.{adlevel; type_; loc} =
      ( Expr.Labelled.Meta.create ~type_ ~loc ~adlevel ~label ()
      , Int_label.next label 
      )
    and g label loc =
      ( Meta.create ~loc ~label ()
      , Int_label.next label
      )
    in 
    Fixed.map_accum_left stmt ~init ~f ~g      
    |> fst



  type associations =
    {exprs: Expr.Labelled.t Int_label.Map.t; stmts: t Int_label.Map.t}

  let empty = {exprs= Int_label.Map.empty; stmts= Int_label.Map.empty}

  let rec associate ?init:(assocs = empty) (stmt : t) =
    associate_pattern
      { assocs with
        stmts=
          Int_label.Map.add_exn assocs.stmts ~key:(label_of stmt) ~data:stmt }
      (Fixed.pattern stmt)

  and associate_pattern assocs = function
    | Fixed.Pattern.Break | Skip | Continue | Return None -> assocs
    | Return (Some e) | TargetPE e ->
        {assocs with exprs= Expr.Labelled.associate ~init:assocs.exprs e}
    | NRFunApp (_, _, args) ->
        { assocs with
          exprs=
            List.fold args ~init:assocs.exprs ~f:(fun accu x ->
                Expr.Labelled.associate ~init:accu x ) }
    | Assignment ((_, idxs), rhs) ->
        let exprs =
          Expr.Labelled.(
            associate rhs
              ~init:(List.fold ~f:associate_index ~init:assocs.exprs idxs))
        in
        {assocs with exprs}
    | IfElse (pred, body, None) | While (pred, body) ->
        let exprs = Expr.Labelled.associate ~init:assocs.exprs pred in
        associate ~init:{assocs with exprs} body
    | IfElse (pred, ts, Some fs) ->
        let exprs = Expr.Labelled.associate ~init:assocs.exprs pred in
        let assocs' = {assocs with exprs} in
        associate ~init:(associate ~init:assocs' ts) fs
    | Decl {decl_type; _} -> associate_possibly_sized_type assocs decl_type
    | For {lower; upper; body; _} ->
        let exprs =
          Expr.Labelled.(
            associate ~init:(associate ~init:assocs.exprs lower) upper)
        in
        let assocs' = {assocs with exprs} in
        associate ~init:assocs' body
    | Block xs | SList xs ->
        List.fold ~f:(fun accu x -> associate ~init:accu x) ~init:assocs xs

  and associate_possibly_sized_type assocs = function
    | Mir_pattern.Sized st ->
        {assocs with exprs= SizedType.associate ~init:assocs.exprs st}
    | Mir_pattern.Unsized _ -> assocs
end

