/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C079C001Part004

/-! NF weak partition development: NAR4C079C001Part005. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nb079_split_alpha_0001 (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    TAlphaWff
      [((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
        ((nb079_alpha_dummy_002 A), z)]
      (Wff.imp (Wff.classEq (Class.cv (nb079_alpha_dummy_002 A))
          (syn_copk (Class.cv (nb079_alpha_dummy_000 A)) (Class.cv (nb079_alpha_dummy_001 A))))
        (Wff.neg (Wff.classMem (syn_cop (Class.cv (nb079_alpha_dummy_000 A))
              (Class.cv (nb079_alpha_dummy_001 A))) A)))
      (Wff.imp (Wff.classEq (Class.cv z) (syn_copk (Class.cv x) (Class.cv y)))
        (Wff.neg (Wff.classMem (syn_cop (Class.cv x) (Class.cv y)) A))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_y_z)
          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_x_z)
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from
                                    (by
                                      unfold nb079_alpha_dummy_009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0006 A)
                                              0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
                                      unfold nb079_alpha_dummy_010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0007 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_007 A) from
                                      (by
                                        unfold nb079_alpha_dummy_007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0004 A)
                                                0)))) (show x ≠ (nb079_alpha_dummy_008 x) from
                                      (by
                                        unfold nb079_alpha_dummy_008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0005 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_005 A)
                                        from (by
                                          unfold nb079_alpha_dummy_005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0002 A) 0))))
                                      (show x ≠ (nb079_alpha_dummy_006 x) from (by
                                          unfold nb079_alpha_dummy_006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0003 x) 0))))
                                      (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000 A) 0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from
        (by
          unfold nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from
                                    (by
                                      unfold nb079_alpha_dummy_009;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0006 A)
                                              0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
                                      unfold nb079_alpha_dummy_010;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb079_support_mem_0007 x)
                                              0)))) (TAlphaVar.there (show
                                      (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_007 A) from
                                      (by
                                        unfold nb079_alpha_dummy_007;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0004 A)
                                                0)))) (show x ≠ (nb079_alpha_dummy_008 x) from
                                      (by
                                        unfold nb079_alpha_dummy_008;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0005 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_005 A)
                                        from (by
                                          unfold nb079_alpha_dummy_005;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0002 A) 0))))
                                      (show x ≠ (nb079_alpha_dummy_006 x) from (by
                                          unfold nb079_alpha_dummy_006;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0003 x) 0))))
                                      (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000 A) 0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from
        (by
          unfold nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from (by
          unfold nb079_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
          unfold nb079_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_017 A) from (by
          unfold nb079_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_018 x) from (by
          unfold nb079_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from (by
          unfold nb079_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
          unfold nb079_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_017 A) from (by
          unfold nb079_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_018 x) from (by
          unfold nb079_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_021 A) from (by
          unfold nb079_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_022 y) from (by
          unfold nb079_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_019 A) from (by
          unfold nb079_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_020 y) from (by
          unfold nb079_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_021 A) from (by
          unfold nb079_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_022 y) from (by
          unfold nb079_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_019 A) from (by
          unfold nb079_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_020 y) from (by
          unfold nb079_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from (by
          unfold nb079_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
          unfold nb079_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_017 A) from (by
          unfold nb079_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_018 x) from (by
          unfold nb079_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_009 A) from (by
          unfold nb079_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0006 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_010 x) from (by
          unfold nb079_alpha_dummy_010;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0007 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_017 A) from (by
          unfold nb079_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0014 A)
                  0)))) (show x ≠ (nb079_alpha_dummy_018 x) from (by
          unfold nb079_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0015 x)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0012
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0010
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0011
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0008
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0009
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0000
                    A)
                  0)))) (show x ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0001
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_021 A) from (by
          unfold nb079_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_022 y) from (by
          unfold nb079_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_019 A) from (by
          unfold nb079_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_020 y) from (by
          unfold nb079_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_001 A) ≠ (nb079_alpha_dummy_021 A) from (by
          unfold nb079_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0026 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_022 y) from (by
          unfold nb079_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0027 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_019 A) from (by
          unfold nb079_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0024 A)
                  0)))) (show y ≠ (nb079_alpha_dummy_020 y) from (by
          unfold nb079_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0025 y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_015 A) from (by
          unfold nb079_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0022
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_016 x y) from (by
          unfold nb079_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0023
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_013 A) from (by
          unfold nb079_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0020
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_014 x y) from (by
          unfold nb079_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0021
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_011 A) from (by
          unfold
            nb079_alpha_dummy_011;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0018
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_012 x y) from (by
          unfold
            nb079_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0019
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_001 A) ≠
        (nb079_alpha_dummy_003 A) from (by
          unfold
            nb079_alpha_dummy_003;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0016
                    A)
                  0)))) (show y ≠ (nb079_alpha_dummy_004 x y) from (by
          unfold
            nb079_alpha_dummy_004;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0017
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_024 A) from
                                      (by
                                        unfold nb079_alpha_dummy_024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0028 A)
                                                1)))) (show x ≠ (nb079_alpha_dummy_026 x y) from
                                      (by
                                        unfold nb079_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb079_support_mem_0030 x y) 1))))
                                    (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_023 A) from (by
                                          unfold nb079_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0028 A) 0))))
                                      (show x ≠ (nb079_alpha_dummy_025 x y) from (by
                                          unfold nb079_alpha_dummy_025;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0030 x y) 0))))
                                      (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_029 A) from (by
          unfold nb079_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0032 A) 0)))) (show x ≠ (nb079_alpha_dummy_030 x y) from
        (by
          unfold nb079_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0033 x y) 0)))) (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_027 A) from (by
          unfold nb079_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0029 A) 0)))) (show x ≠ (nb079_alpha_dummy_028 x y) from
        (by
          unfold nb079_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0031 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪
                                        ((Class.cv (nb079_alpha_dummy_001 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_024 A) ≠ (nb079_alpha_dummy_031 A) from (by
          unfold nb079_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079_alpha_dummy_026 x y) ≠
        (nb079_alpha_dummy_033 x y) from (by
          unfold nb079_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079_alpha_dummy_024 A) ≠ (nb079_alpha_dummy_032 A) from (by
          unfold nb079_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079_alpha_dummy_026 x y) ≠
        (nb079_alpha_dummy_034 x y) from (by
          unfold nb079_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031
        A) ≠ (nb079_alpha_dummy_038 A) from (by
          unfold
            nb079_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_041 x y) from (by
          unfold
            nb079_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_037 A) from (by
          unfold
            nb079_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_040 x y) from (by
          unfold
            nb079_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold
            nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold
            nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A),
        (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)),
        ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A),
        y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_038 A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A),
        (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)),
        ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A),
        y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_049 A) from (by
          unfold
            nb079_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_050 x y) from (by
          unfold
            nb079_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_038
        A) ≠ (nb079_alpha_dummy_049 A) from (by
          unfold
            nb079_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_050 x y) from (by
          unfold
            nb079_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠ (nb079_alpha_dummy_051 A) from (by
          unfold
            nb079_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_052 x y) from (by
          unfold
            nb079_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_051 A) from (by
          unfold
            nb079_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_052 x y) from (by
          unfold
            nb079_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)),
        ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
        ((nb079_alpha_dummy_002 A), z)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)),
        ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
        ((nb079_alpha_dummy_002 A), z)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_024 A) from
                                      (by
                                        unfold nb079_alpha_dummy_024;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb079_support_mem_0028 A)
                                                1)))) (show x ≠ (nb079_alpha_dummy_026 x y) from
                                      (by
                                        unfold nb079_alpha_dummy_026;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb079_support_mem_0030 x y) 1))))
                                    (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_023 A) from (by
                                          unfold nb079_alpha_dummy_023;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0028 A) 0))))
                                      (show x ≠ (nb079_alpha_dummy_025 x y) from (by
                                          unfold nb079_alpha_dummy_025;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb079_support_mem_0030 x y) 0))))
                                      (TAlphaVar.there (show (nb079_alpha_dummy_000 A) ≠
        (nb079_alpha_dummy_029 A) from (by
          unfold nb079_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0032 A) 0)))) (show x ≠ (nb079_alpha_dummy_030 x y) from
        (by
          unfold nb079_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0033 x y) 0)))) (TAlphaVar.there (show
        (nb079_alpha_dummy_000 A) ≠ (nb079_alpha_dummy_027 A) from (by
          unfold nb079_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0029 A) 0)))) (show x ≠ (nb079_alpha_dummy_028 x y) from
        (by
          unfold nb079_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0031 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb079_alpha_dummy_000 A))).fv ∪
                                        ((Class.cv (nb079_alpha_dummy_001 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_024 A) ≠ (nb079_alpha_dummy_031 A) from (by
          unfold nb079_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 0)))) (show (nb079_alpha_dummy_026 x y) ≠
        (nb079_alpha_dummy_033 x y) from (by
          unfold nb079_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y) 0)))) (TAlphaVar.there (show
        (nb079_alpha_dummy_024 A) ≠ (nb079_alpha_dummy_032 A) from (by
          unfold nb079_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0034 A) 1)))) (show (nb079_alpha_dummy_026 x y) ≠
        (nb079_alpha_dummy_034 x y) from (by
          unfold nb079_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0035 x y)
                  1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_024 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_026 x y))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031
        A) ≠ (nb079_alpha_dummy_038 A) from (by
          unfold
            nb079_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  1)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_041 x y) from (by
          unfold
            nb079_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  1)))) (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_037 A) from (by
          unfold
            nb079_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0038
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_040 x y) from (by
          unfold
            nb079_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0039
                    x y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold
            nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold
            nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A),
        (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)),
        ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A),
        y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb079_alpha_dummy_038 A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0042
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0043
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0040
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0041
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_045 A) from (by
          unfold
            nb079_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0046
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_046 x y) from (by
          unfold
            nb079_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0047
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_043 A) from (by
          unfold
            nb079_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0044
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_044 x y) from (by
          unfold
            nb079_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0045
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_039 A), (nb079_alpha_dummy_042 x y)), ((nb079_alpha_dummy_038 A),
        (nb079_alpha_dummy_041 x y)), ((nb079_alpha_dummy_037 A), (nb079_alpha_dummy_040 x y)),
        ((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)), ((nb079_alpha_dummy_001 A),
        y), ((nb079_alpha_dummy_000 A), x), ((nb079_alpha_dummy_002 A), z)] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb079_alpha_dummy_031 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_049 A) from (by
          unfold
            nb079_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_050 x y) from (by
          unfold
            nb079_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_038
        A) ≠ (nb079_alpha_dummy_049 A) from (by
          unfold
            nb079_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0050
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_050 x y) from (by
          unfold
            nb079_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0051
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_038 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0048
                    A)
                  0)))) (show (nb079_alpha_dummy_041 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0049
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb079_alpha_dummy_031
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb079_alpha_dummy_033 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠ (nb079_alpha_dummy_051 A) from (by
          unfold
            nb079_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_052 x y) from (by
          unfold
            nb079_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_039
        A) ≠ (nb079_alpha_dummy_051 A) from (by
          unfold
            nb079_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0054
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_052 x y) from (by
          unfold
            nb079_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0055
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb079_alpha_dummy_039 A) ≠
        (nb079_alpha_dummy_047 A) from (by
          unfold
            nb079_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0052
                    A)
                  0)))) (show (nb079_alpha_dummy_042 x y) ≠ (nb079_alpha_dummy_048 x y) from (by
          unfold
            nb079_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0053
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)),
        ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
        ((nb079_alpha_dummy_002 A), z)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036 A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037 x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb079_alpha_dummy_031 A) ≠
        (nb079_alpha_dummy_035 A) from (by
          unfold nb079_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0036
                    A)
                  0)))) (show (nb079_alpha_dummy_033 x y) ≠ (nb079_alpha_dummy_036 x y) from (by
          unfold nb079_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb079_support_mem_0037
                    x y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb079_alpha_dummy_035 A), (nb079_alpha_dummy_036 x y)), ((nb079_alpha_dummy_031 A),
        (nb079_alpha_dummy_033 x y)), ((nb079_alpha_dummy_032 A), (nb079_alpha_dummy_034 x y)),
        ((nb079_alpha_dummy_024 A), (nb079_alpha_dummy_026 x y)), ((nb079_alpha_dummy_023 A),
        (nb079_alpha_dummy_025 x y)), ((nb079_alpha_dummy_029 A), (nb079_alpha_dummy_030 x y)),
        ((nb079_alpha_dummy_027 A), (nb079_alpha_dummy_028 x y)),
        ((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
        ((nb079_alpha_dummy_002 A), z)] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb079_split_alpha_0000 x y z A))))))))
        (TAlphaClass.refl_of_reflOn
          [((nb079_alpha_dummy_001 A), y), ((nb079_alpha_dummy_000 A), x),
            ((nb079_alpha_dummy_002 A), z)]
          A (nb079_focused_refl_0000 x y z A dv_A_x dv_A_y dv_A_z)))))

@[expose]
noncomputable def nominal_df_qkrel (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cqkrel A) (.cab z (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
                (.classMem (syn_cop (.cv x) (.cv y)) A)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg
              (nb079_split_alpha_0001 x y z A dv_A_x dv_A_y dv_A_z dv_x_y dv_x_z dv_y_z)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
