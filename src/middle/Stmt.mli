open Core_kernel
open Common

module Fixed : sig
  module Pattern : sig
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
    [@@deriving sexp, hash, compare]

    include Pattern.S2 with type ('a, 'b) t := ('a, 'b) t
  end

  include Fix.S2 with module First = Expr.Fixed and module Pattern := Pattern

  val map_accum_left :
       f:('state -> 'a -> 'c * 'state)
    -> g:('state -> 'b -> 'd * 'state)
    -> init:'state
    -> ('a, 'b) t
    -> ('c, 'd) t * 'state

  val map_accum_right :
       f:('state -> 'a -> 'c * 'state)
    -> g:('state -> 'b -> 'd * 'state)
    -> init:'state
    -> ('a, 'b) t
    -> ('c, 'd) t * 'state
end

module NoMeta : sig
  module Meta : sig
    type t = unit [@@deriving compare, sexp, hash]

    include Meta.S with type t := t
  end

  include
    Specialized.S
    with module Meta := Meta
     and type t = (Expr.NoMeta.Meta.t, Meta.t) Fixed.t

  val remove_meta : ('a, 'b) Fixed.t -> t
end

module Located : sig
  module Meta : sig
    type t = (Location_span.t sexp_opaque[@compare.ignore])
    [@@deriving compare, sexp, hash]

    include Meta.S with type t := t
  end

  include
    Specialized.S
    with module Meta := Meta
     and type t = (Expr.Typed.Meta.t, Meta.t) Fixed.t

  val loc_of : t -> Location_span.t
end

module Labelled : sig
  module Meta : sig
    type t =
      { loc: Location_span.t sexp_opaque [@compare.ignore]
      ; label: Int_label.t [@compare.ignore] }
    [@@deriving compare, create, sexp, hash]

    include Meta.S with type t := t

    val label : t -> Int_label.t
    val loc : t -> Location_span.t
  end

  include
    Specialized.S
    with module Meta := Meta
     and type t = (Expr.Labelled.Meta.t, Meta.t) Fixed.t

  val loc_of : t -> Location_span.t
  val label_of : t -> Int_label.t
  val label : ?init:int -> Located.t -> t

  type associations =
    {exprs: Expr.Labelled.t Int_label.Map.t; stmts: t Int_label.Map.t}

  val associate : ?init:associations -> t -> associations
end



