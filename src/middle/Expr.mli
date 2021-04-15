open Core_kernel
open Common

module Fixed : sig
  module Pattern : sig
    type litType = Int | Real | Str [@@deriving sexp, hash, compare]

    type 'exprs t =
      | Var of string
      | Lit of litType * string
      | FunApp of Fun_kind.t * 'exprs list
      | TernaryIf of 'exprs * 'exprs * 'exprs
      | EAnd of 'exprs * 'exprs
      | EOr of 'exprs * 'exprs
      | Indexed of 'exprs * 'exprs Index.t list
    [@@deriving sexp, hash, compare]

    include Pattern.S with type 'exprs t := 'exprs t
  end

  include Fixed.S with module Pattern := Pattern
end

module NoMeta : sig
  module Meta : sig
    type t = unit [@@deriving compare, sexp, hash]

    include Specialized.Meta with type t := unit
  end

  include Specialized.S with module Meta := Meta and type t = Meta.t Fixed.t

  val remove_meta : 'exprs Fixed.t -> t
end

module Typed : sig
  module Meta : sig
    type t =
      { type_: UnsizedType.t
      ; loc: Location_span.t sexp_opaque [@compare.ignore]
      ; adlevel: UnsizedType.autodifftype }
    [@@deriving compare, create, sexp, hash]

    include Specialized.Meta with type t := t
  end

  include Specialized.S with module Meta := Meta and type t = Meta.t Fixed.t

  val type_of : t -> UnsizedType.t
  val loc_of : t -> Location_span.t
  val adlevel_of : t -> UnsizedType.autodifftype
end

module Labelled : sig
  module Meta : sig
    type t =
      { type_: UnsizedType.t
      ; loc: Location_span.t sexp_opaque [@compare.ignore]
      ; adlevel: UnsizedType.autodifftype
      ; label: Label.Int_label.t }
    [@@deriving compare, create, sexp, hash]

    include Specialized.Meta with type t := t
  end

  include Specialized.S with module Meta := Meta and type t = Meta.t Fixed.t

  val type_of : t -> UnsizedType.t
  val loc_of : t -> Location_span.t
  val adlevel_of : t -> UnsizedType.autodifftype
  val label_of : t -> Label.Int_label.t
  val label : ?init:int -> Typed.t -> t
  val associate : ?init:t Label.Int_label.Map.t -> t -> t Label.Int_label.Map.t

  val associate_index :
    t Label.Int_label.Map.t -> t Index.t -> t Label.Int_label.Map.t
end

module Helpers : sig
  val int : int -> Typed.t
  val float : float -> Typed.t
  val str : string -> Typed.t
  val zero : Typed.t
  val one : Typed.t
  val binop : Typed.t -> Operator.t -> Typed.t -> Typed.t
  val loop_bottom : Typed.t

  val internal_funapp :
    Internal_fun.t -> 'exprs Fixed.t list -> 'exprs -> 'exprs Fixed.t

  val contains_fn_kind :
    (Fun_kind.t -> bool) -> ?init:bool -> 'exprs Fixed.t -> bool

  val infer_type_of_indexed :
    UnsizedType.t -> 'exprs Index.t list -> UnsizedType.t

  val add_int_index : Typed.t -> Typed.t Index.t -> Typed.t
  val collect_indices : 'exprs Fixed.t -> 'exprs Fixed.t Index.t list
end
