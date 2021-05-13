open Frontend
open Middle
open Core_kernel
open Ast_to_Mir

let%expect_test "Operator-assign example" =
  Frontend_utils.typed_ast_of_string_exn
    {|
        model {
          real r;
          vector[2] x[4];
          x[1] ./= r;
        }
      |}
  |> trans_prog ""
  |> (fun Program.({log_prob; _}) -> log_prob)
  |> Fmt.strf "@[<v>%a@]" (Fmt.list ~sep:Fmt.cut Stmt.Located.pp)
  |> print_endline ;
  [%expect
    {|
      {
        real r;
        array[vector[2], 4] x;
        x[1] = (x[1] ./ r);
      } |}]

let mir_from_string s =
  Frontend_utils.typed_ast_of_string_exn s |> trans_prog ""

let%expect_test "Prefix-Op-Example" =
  let mir =
    mir_from_string
      {|
        model {
          int i;
          if (i < -1)
            print("Badger");
        }
      |}
  in
  let op = mir.log_prob in
  print_s [%sexp (op : Stmt.Located.t list)] ;
  (* Perhaps this is producing too many nested lists. XXX*)
  [%expect
    {|
      (((pattern
         (Block
          (((pattern
             (Decl (decl_adtype AutoDiffable) (decl_id i) (decl_type (Sized SInt))))
            (meta
             ((begin_loc
               ((filename string) (line_num 3) (col_num 10) (included_from ())))
              (end_loc
               ((filename string) (line_num 3) (col_num 16) (included_from ()))))))
           ((pattern
             (IfElse
              ((pattern
                (FunApp (StanLib Less__ FnPlain SoA)
                 (((pattern (Var i))
                   (meta
                    ((type_ UInt)
                     (loc
                      ((begin_loc
                        ((filename string) (line_num 4) (col_num 14)
                         (included_from ())))
                       (end_loc
                        ((filename string) (line_num 4) (col_num 15)
                         (included_from ())))))
                     (adlevel DataOnly))))
                  ((pattern
                    (FunApp (StanLib PMinus__ FnPlain SoA)
                     (((pattern (Lit Int 1))
                       (meta
                        ((type_ UInt)
                         (loc
                          ((begin_loc
                            ((filename string) (line_num 4) (col_num 19)
                             (included_from ())))
                           (end_loc
                            ((filename string) (line_num 4) (col_num 20)
                             (included_from ())))))
                         (adlevel DataOnly)))))))
                   (meta
                    ((type_ UInt)
                     (loc
                      ((begin_loc
                        ((filename string) (line_num 4) (col_num 19)
                         (included_from ())))
                       (end_loc
                        ((filename string) (line_num 4) (col_num 20)
                         (included_from ())))))
                     (adlevel DataOnly)))))))
               (meta
                ((type_ UInt)
                 (loc
                  ((begin_loc
                    ((filename string) (line_num 4) (col_num 14)
                     (included_from ())))
                   (end_loc
                    ((filename string) (line_num 4) (col_num 20)
                     (included_from ())))))
                 (adlevel DataOnly))))
              ((pattern
                (NRFunApp (CompilerInternal FnPrint)
                 (((pattern (Lit Str Badger))
                   (meta
                    ((type_ UReal)
                     (loc
                      ((begin_loc
                        ((filename string) (line_num 5) (col_num 12)
                         (included_from ())))
                       (end_loc
                        ((filename string) (line_num 5) (col_num 28)
                         (included_from ())))))
                     (adlevel DataOnly)))))))
               (meta
                ((begin_loc
                  ((filename string) (line_num 5) (col_num 12) (included_from ())))
                 (end_loc
                  ((filename string) (line_num 5) (col_num 28) (included_from ()))))))
              ()))
            (meta
             ((begin_loc
               ((filename string) (line_num 4) (col_num 10) (included_from ())))
              (end_loc
               ((filename string) (line_num 5) (col_num 28) (included_from ())))))))))
        (meta
         ((begin_loc
           ((filename string) (line_num 3) (col_num 10) (included_from ())))
          (end_loc
           ((filename string) (line_num 3) (col_num 16) (included_from ()))))))) |}]

let%expect_test "read data" =
  let m = mir_from_string "data { matrix[10, 20] mat[5]; }" in
  print_s [%sexp (m.prepare_data : Stmt.Located.t list)] ;
  [%expect
    {|
    (((pattern
       (Decl (decl_adtype DataOnly) (decl_id mat)
        (decl_type
         (Sized
          (SArray
           (SMatrix SoA
            ((pattern (Lit Int 10))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 14)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 16)
                   (included_from ())))))
               (adlevel DataOnly))))
            ((pattern (Lit Int 20))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 18)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 20)
                   (included_from ())))))
               (adlevel DataOnly)))))
           ((pattern (Lit Int 5))
            (meta
             ((type_ UInt)
              (loc
               ((begin_loc
                 ((filename string) (line_num 1) (col_num 26) (included_from ())))
                (end_loc
                 ((filename string) (line_num 1) (col_num 27) (included_from ())))))
              (adlevel DataOnly)))))))))
      (meta
       ((begin_loc
         ((filename string) (line_num 1) (col_num 7) (included_from ())))
        (end_loc
         ((filename string) (line_num 1) (col_num 29) (included_from ()))))))) |}]

let%expect_test "read param" =
  let m = mir_from_string "parameters { matrix<lower=0>[10, 20] mat[5]; }" in
  print_s [%sexp (m.log_prob : Stmt.Located.t list)] ;
  [%expect
    {|
    (((pattern
       (Decl (decl_adtype AutoDiffable) (decl_id mat)
        (decl_type
         (Sized
          (SArray
           (SMatrix SoA
            ((pattern (Lit Int 10))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 29)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 31)
                   (included_from ())))))
               (adlevel DataOnly))))
            ((pattern (Lit Int 20))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 33)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 35)
                   (included_from ())))))
               (adlevel DataOnly)))))
           ((pattern (Lit Int 5))
            (meta
             ((type_ UInt)
              (loc
               ((begin_loc
                 ((filename string) (line_num 1) (col_num 41) (included_from ())))
                (end_loc
                 ((filename string) (line_num 1) (col_num 42) (included_from ())))))
              (adlevel DataOnly)))))))))
      (meta
       ((begin_loc
         ((filename string) (line_num 1) (col_num 13) (included_from ())))
        (end_loc
         ((filename string) (line_num 1) (col_num 44) (included_from ()))))))) |}]

let%expect_test "gen quant" =
  let m =
    mir_from_string "generated quantities { matrix<lower=0>[10, 20] mat[5]; }"
  in
  print_s [%sexp (m.generate_quantities : Stmt.Located.t list)] ;
  [%expect
    {|
    (((pattern
       (IfElse
        ((pattern
          (FunApp (StanLib PNot__ FnPlain SoA)
           (((pattern
              (EOr
               ((pattern (Var emit_transformed_parameters__))
                (meta
                 ((type_ UInt)
                  (loc
                   ((begin_loc
                     ((filename "") (line_num 0) (col_num 0) (included_from ())))
                    (end_loc
                     ((filename "") (line_num 0) (col_num 0) (included_from ())))))
                  (adlevel DataOnly))))
               ((pattern (Var emit_generated_quantities__))
                (meta
                 ((type_ UInt)
                  (loc
                   ((begin_loc
                     ((filename "") (line_num 0) (col_num 0) (included_from ())))
                    (end_loc
                     ((filename "") (line_num 0) (col_num 0) (included_from ())))))
                  (adlevel DataOnly))))))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename "") (line_num 0) (col_num 0) (included_from ())))
                 (end_loc
                  ((filename "") (line_num 0) (col_num 0) (included_from ())))))
               (adlevel DataOnly)))))))
         (meta
          ((type_ UInt)
           (loc
            ((begin_loc
              ((filename "") (line_num 0) (col_num 0) (included_from ())))
             (end_loc
              ((filename "") (line_num 0) (col_num 0) (included_from ())))))
           (adlevel DataOnly))))
        ((pattern (Return ()))
         (meta
          ((begin_loc
            ((filename "") (line_num 0) (col_num 0) (included_from ())))
           (end_loc ((filename "") (line_num 0) (col_num 0) (included_from ()))))))
        ()))
      (meta
       ((begin_loc ((filename "") (line_num 0) (col_num 0) (included_from ())))
        (end_loc ((filename "") (line_num 0) (col_num 0) (included_from ()))))))
     ((pattern
       (IfElse
        ((pattern
          (FunApp (StanLib PNot__ FnPlain SoA)
           (((pattern (Var emit_generated_quantities__))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename "") (line_num 0) (col_num 0) (included_from ())))
                 (end_loc
                  ((filename "") (line_num 0) (col_num 0) (included_from ())))))
               (adlevel DataOnly)))))))
         (meta
          ((type_ UInt)
           (loc
            ((begin_loc
              ((filename "") (line_num 0) (col_num 0) (included_from ())))
             (end_loc
              ((filename "") (line_num 0) (col_num 0) (included_from ())))))
           (adlevel DataOnly))))
        ((pattern (Return ()))
         (meta
          ((begin_loc
            ((filename "") (line_num 0) (col_num 0) (included_from ())))
           (end_loc ((filename "") (line_num 0) (col_num 0) (included_from ()))))))
        ()))
      (meta
       ((begin_loc ((filename "") (line_num 0) (col_num 0) (included_from ())))
        (end_loc ((filename "") (line_num 0) (col_num 0) (included_from ()))))))
     ((pattern
       (Decl (decl_adtype DataOnly) (decl_id mat)
        (decl_type
         (Sized
          (SArray
           (SMatrix SoA
            ((pattern (Lit Int 10))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 39)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 41)
                   (included_from ())))))
               (adlevel DataOnly))))
            ((pattern (Lit Int 20))
             (meta
              ((type_ UInt)
               (loc
                ((begin_loc
                  ((filename string) (line_num 1) (col_num 43)
                   (included_from ())))
                 (end_loc
                  ((filename string) (line_num 1) (col_num 45)
                   (included_from ())))))
               (adlevel DataOnly)))))
           ((pattern (Lit Int 5))
            (meta
             ((type_ UInt)
              (loc
               ((begin_loc
                 ((filename string) (line_num 1) (col_num 51) (included_from ())))
                (end_loc
                 ((filename string) (line_num 1) (col_num 52) (included_from ())))))
              (adlevel DataOnly)))))))))
      (meta
       ((begin_loc
         ((filename string) (line_num 1) (col_num 23) (included_from ())))
        (end_loc
         ((filename string) (line_num 1) (col_num 54) (included_from ()))))))
     ((pattern
       (For (loopvar sym1__)
        (lower
         ((pattern (Lit Int 1))
          (meta
           ((type_ UInt)
            (loc
             ((begin_loc
               ((filename "") (line_num 0) (col_num 0) (included_from ())))
              (end_loc
               ((filename "") (line_num 0) (col_num 0) (included_from ())))))
            (adlevel DataOnly)))))
        (upper
         ((pattern (Lit Int 5))
          (meta
           ((type_ UInt)
            (loc
             ((begin_loc
               ((filename string) (line_num 1) (col_num 51) (included_from ())))
              (end_loc
               ((filename string) (line_num 1) (col_num 52) (included_from ())))))
            (adlevel DataOnly)))))
        (body
         ((pattern
           (Block
            (((pattern
               (For (loopvar sym2__)
                (lower
                 ((pattern (Lit Int 1))
                  (meta
                   ((type_ UInt)
                    (loc
                     ((begin_loc
                       ((filename "") (line_num 0) (col_num 0)
                        (included_from ())))
                      (end_loc
                       ((filename "") (line_num 0) (col_num 0)
                        (included_from ())))))
                    (adlevel DataOnly)))))
                (upper
                 ((pattern (Lit Int 10))
                  (meta
                   ((type_ UInt)
                    (loc
                     ((begin_loc
                       ((filename string) (line_num 1) (col_num 39)
                        (included_from ())))
                      (end_loc
                       ((filename string) (line_num 1) (col_num 41)
                        (included_from ())))))
                    (adlevel DataOnly)))))
                (body
                 ((pattern
                   (Block
                    (((pattern
                       (For (loopvar sym3__)
                        (lower
                         ((pattern (Lit Int 1))
                          (meta
                           ((type_ UInt)
                            (loc
                             ((begin_loc
                               ((filename "") (line_num 0) (col_num 0)
                                (included_from ())))
                              (end_loc
                               ((filename "") (line_num 0) (col_num 0)
                                (included_from ())))))
                            (adlevel DataOnly)))))
                        (upper
                         ((pattern (Lit Int 20))
                          (meta
                           ((type_ UInt)
                            (loc
                             ((begin_loc
                               ((filename string) (line_num 1) (col_num 43)
                                (included_from ())))
                              (end_loc
                               ((filename string) (line_num 1) (col_num 45)
                                (included_from ())))))
                            (adlevel DataOnly)))))
                        (body
                         ((pattern
                           (Block
                            (((pattern
                               (NRFunApp
                                (CompilerInternal (FnCheck greater_or_equal))
                                (((pattern
                                   (Lit Str "mat[sym1__, sym2__, sym3__]"))
                                  (meta
                                   ((type_ UInt)
                                    (loc
                                     ((begin_loc
                                       ((filename "") (line_num 0) (col_num 0)
                                        (included_from ())))
                                      (end_loc
                                       ((filename "") (line_num 0) (col_num 0)
                                        (included_from ())))))
                                    (adlevel DataOnly))))
                                 ((pattern
                                   (Indexed
                                    ((pattern (Var mat))
                                     (meta
                                      ((type_ (UArray UMatrix))
                                       (loc
                                        ((begin_loc
                                          ((filename string) (line_num 1)
                                           (col_num 23) (included_from ())))
                                         (end_loc
                                          ((filename string) (line_num 1)
                                           (col_num 54) (included_from ())))))
                                       (adlevel DataOnly))))
                                    ((Single
                                      ((pattern (Var sym1__))
                                       (meta
                                        ((type_ UInt)
                                         (loc
                                          ((begin_loc
                                            ((filename string) (line_num 1)
                                             (col_num 23) (included_from ())))
                                           (end_loc
                                            ((filename string) (line_num 1)
                                             (col_num 54) (included_from ())))))
                                         (adlevel DataOnly)))))
                                     (Single
                                      ((pattern (Var sym2__))
                                       (meta
                                        ((type_ UInt)
                                         (loc
                                          ((begin_loc
                                            ((filename string) (line_num 1)
                                             (col_num 23) (included_from ())))
                                           (end_loc
                                            ((filename string) (line_num 1)
                                             (col_num 54) (included_from ())))))
                                         (adlevel DataOnly)))))
                                     (Single
                                      ((pattern (Var sym3__))
                                       (meta
                                        ((type_ UInt)
                                         (loc
                                          ((begin_loc
                                            ((filename string) (line_num 1)
                                             (col_num 23) (included_from ())))
                                           (end_loc
                                            ((filename string) (line_num 1)
                                             (col_num 54) (included_from ())))))
                                         (adlevel DataOnly))))))))
                                  (meta
                                   ((type_ UReal)
                                    (loc
                                     ((begin_loc
                                       ((filename string) (line_num 1)
                                        (col_num 23) (included_from ())))
                                      (end_loc
                                       ((filename string) (line_num 1)
                                        (col_num 54) (included_from ())))))
                                    (adlevel DataOnly))))
                                 ((pattern (Lit Int 0))
                                  (meta
                                   ((type_ UInt)
                                    (loc
                                     ((begin_loc
                                       ((filename string) (line_num 1)
                                        (col_num 36) (included_from ())))
                                      (end_loc
                                       ((filename string) (line_num 1)
                                        (col_num 37) (included_from ())))))
                                    (adlevel DataOnly)))))))
                              (meta
                               ((begin_loc
                                 ((filename string) (line_num 1) (col_num 23)
                                  (included_from ())))
                                (end_loc
                                 ((filename string) (line_num 1) (col_num 54)
                                  (included_from ())))))))))
                          (meta
                           ((begin_loc
                             ((filename string) (line_num 1) (col_num 23)
                              (included_from ())))
                            (end_loc
                             ((filename string) (line_num 1) (col_num 54)
                              (included_from ())))))))))
                      (meta
                       ((begin_loc
                         ((filename string) (line_num 1) (col_num 23)
                          (included_from ())))
                        (end_loc
                         ((filename string) (line_num 1) (col_num 54)
                          (included_from ())))))))))
                  (meta
                   ((begin_loc
                     ((filename string) (line_num 1) (col_num 23)
                      (included_from ())))
                    (end_loc
                     ((filename string) (line_num 1) (col_num 54)
                      (included_from ())))))))))
              (meta
               ((begin_loc
                 ((filename string) (line_num 1) (col_num 23) (included_from ())))
                (end_loc
                 ((filename string) (line_num 1) (col_num 54) (included_from ())))))))))
          (meta
           ((begin_loc
             ((filename string) (line_num 1) (col_num 23) (included_from ())))
            (end_loc
             ((filename string) (line_num 1) (col_num 54) (included_from ())))))))))
      (meta
       ((begin_loc
         ((filename string) (line_num 1) (col_num 23) (included_from ())))
        (end_loc
         ((filename string) (line_num 1) (col_num 54) (included_from ()))))))) |}]
