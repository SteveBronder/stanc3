(** Translate from the AST to the MIR *)

val trans_prog : string -> Ast.typed_program -> Middle.Program.Typed.t
