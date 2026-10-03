/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C081C001Part004

/-! NF weak partition development: NAR4C081C001Part005. -/


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
noncomputable def nb081_split_alpha_0001 (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
      (Wff.imp (Wff.classEq (Class.cv (nb081_alpha_dummy_002 A))
          (syn_cop (Class.cv (nb081_alpha_dummy_000 A)) (Class.cv (nb081_alpha_dummy_001 A))))
        (Wff.neg (Wff.classMem (syn_copk (Class.cv (nb081_alpha_dummy_000 A))
              (Class.cv (nb081_alpha_dummy_001 A))) A)))
      (Wff.imp (Wff.classEq (Class.cv (nb081_alpha_dummy_003 x y A))
          (syn_cop (Class.cv x) (Class.cv y)))
        (Wff.neg (Wff.classMem (syn_copk (Class.cv x) (Class.cv y)) A))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_002 A) from (by
                unfold nb081_alpha_dummy_002;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0002 A) 0)))))
          (Ne.symm (show y ≠ (nb081_alpha_dummy_003 x y A) from (by
                unfold nb081_alpha_dummy_003;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0003 x y A) 0)))))
          (TAlphaVar.there (Ne.symm
              (show (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_002 A) from (by
                  unfold nb081_alpha_dummy_002;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0000 A) 0)))))
            (Ne.symm (show x ≠ (nb081_alpha_dummy_003 x y A) from (by
                  unfold nb081_alpha_dummy_003;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb081_support_mem_0001 x y A) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_005 A) from
                                    (by
                                      unfold nb081_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0004 A)
                                              1)))) (show x ≠ (nb081_alpha_dummy_007 x y) from
                                    (by
                                      unfold nb081_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0006 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_004 A) from
                                      (by
                                        unfold nb081_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0004 A)
                                                0)))) (show x ≠ (nb081_alpha_dummy_006 x y) from
                                      (by
                                        unfold nb081_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb081_support_mem_0006 x y) 0))))
                                    (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_010 A) from (by
                                          unfold nb081_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0008 A) 0))))
                                      (show x ≠ (nb081_alpha_dummy_011 x y) from (by
                                          unfold nb081_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0009 x y) 0))))
                                      (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_008 A) from (by
          unfold nb081_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0005 A) 0)))) (show x ≠ (nb081_alpha_dummy_009 x y) from
        (by
          unfold nb081_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
                                      ((Class.cv (nb081_alpha_dummy_001 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_005 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_007 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A),
        y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x
        y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A),
        y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003
        x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_005 A) from
                                    (by
                                      unfold nb081_alpha_dummy_005;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0004 A)
                                              1)))) (show x ≠ (nb081_alpha_dummy_007 x y) from
                                    (by
                                      unfold nb081_alpha_dummy_007;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb081_support_mem_0006 x y)
                                              1)))) (TAlphaVar.there (show
                                      (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_004 A) from
                                      (by
                                        unfold nb081_alpha_dummy_004;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0004 A)
                                                0)))) (show x ≠ (nb081_alpha_dummy_006 x y) from
                                      (by
                                        unfold nb081_alpha_dummy_006;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb081_support_mem_0006 x y) 0))))
                                    (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_010 A) from (by
                                          unfold nb081_alpha_dummy_010;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0008 A) 0))))
                                      (show x ≠ (nb081_alpha_dummy_011 x y) from (by
                                          unfold nb081_alpha_dummy_011;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0009 x y) 0))))
                                      (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_008 A) from (by
          unfold nb081_alpha_dummy_008;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0005 A) 0)))) (show x ≠ (nb081_alpha_dummy_009 x y) from
        (by
          unfold nb081_alpha_dummy_009;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0007 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb081_alpha_dummy_000 A))).fv ∪
                                      ((Class.cv (nb081_alpha_dummy_001 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv x)).fv ∪ ((Class.cv y)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb081_alpha_dummy_005 A) ≠
        (nb081_alpha_dummy_012 A) from (by
          unfold nb081_alpha_dummy_012;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 0)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_014 x y) from (by
          unfold nb081_alpha_dummy_014;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_005 A) ≠ (nb081_alpha_dummy_013 A) from (by
          unfold nb081_alpha_dummy_013;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0010 A) 1)))) (show (nb081_alpha_dummy_007 x y) ≠
        (nb081_alpha_dummy_015 x y) from (by
          unfold nb081_alpha_dummy_015;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0011 x y) 1)))) (TAlphaVar.here _ _ _)))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_005 A))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_007 x y))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_019 A) from (by
          unfold
            nb081_alpha_dummy_019;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  1)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_022 x y) from (by
          unfold
            nb081_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  1)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_018 A) from (by
          unfold
            nb081_alpha_dummy_018;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0014
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_021 x y) from (by
          unfold
            nb081_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0015
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold
            nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012
                    A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold
            nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A),
        y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x
        y A))] (syn_c1c) (by
          simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0018
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0019
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0016
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0017
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_026 A) from (by
          unfold
            nb081_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0022
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_027 x y) from (by
          unfold
            nb081_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0023
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_024 A) from (by
          unfold
            nb081_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0020
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_025 x y) from (by
          unfold
            nb081_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0021
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_020 A), (nb081_alpha_dummy_023 x y)), ((nb081_alpha_dummy_019 A),
        (nb081_alpha_dummy_022 x y)), ((nb081_alpha_dummy_018 A), (nb081_alpha_dummy_021 x y)),
        ((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)), ((nb081_alpha_dummy_001 A),
        y), ((nb081_alpha_dummy_000 A), x), ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003
        x y A))] (syn_c0) (by
          simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb081_alpha_dummy_012 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_019
        A) ≠ (nb081_alpha_dummy_030 A) from (by
          unfold
            nb081_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0026
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_031 x y) from (by
          unfold
            nb081_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0027
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_019 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0024
                    A)
                  0)))) (show (nb081_alpha_dummy_022 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0025
                    x
                    y)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb081_alpha_dummy_012
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb081_alpha_dummy_014 x y))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_020
        A) ≠ (nb081_alpha_dummy_032 A) from (by
          unfold
            nb081_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0030
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_033 x y) from (by
          unfold
            nb081_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0031
                    x
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_020 A) ≠
        (nb081_alpha_dummy_028 A) from (by
          unfold
            nb081_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0028
                    A)
                  0)))) (show (nb081_alpha_dummy_023 x y) ≠ (nb081_alpha_dummy_029 x y) from (by
          unfold
            nb081_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0029
                    x
                    y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_012 A) ≠ (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x y)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb081_alpha_dummy_012 A) ≠
        (nb081_alpha_dummy_016 A) from (by
          unfold nb081_alpha_dummy_016;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0012 A)
                  0)))) (show (nb081_alpha_dummy_014 x y) ≠ (nb081_alpha_dummy_017 x y) from (by
          unfold nb081_alpha_dummy_017;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0013 x
                    y)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb081_alpha_dummy_016 A), (nb081_alpha_dummy_017 x y)), ((nb081_alpha_dummy_012 A),
        (nb081_alpha_dummy_014 x y)), ((nb081_alpha_dummy_013 A), (nb081_alpha_dummy_015 x y)),
        ((nb081_alpha_dummy_005 A), (nb081_alpha_dummy_007 x y)), ((nb081_alpha_dummy_004 A),
        (nb081_alpha_dummy_006 x y)), ((nb081_alpha_dummy_010 A), (nb081_alpha_dummy_011 x y)),
        ((nb081_alpha_dummy_008 A), (nb081_alpha_dummy_009 x y)),
        ((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
        ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))] (syn_cnnc) (by
          simp only [fv_syn_cnnc]))))))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb081_split_alpha_0000 x y A)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from
                                      (by
                                        unfold nb081_alpha_dummy_046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0048 A)
                                                0)))) (show x ≠ (nb081_alpha_dummy_047 x) from
                                      (by
                                        unfold nb081_alpha_dummy_047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0049 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_044 A)
                                        from (by
                                          unfold nb081_alpha_dummy_044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0046 A) 0))))
                                      (show x ≠ (nb081_alpha_dummy_045 x) from (by
                                          unfold nb081_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0047 x) 0))))
                                      (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_042 A) from (by
          unfold nb081_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0044 A) 0)))) (show x ≠ (nb081_alpha_dummy_043 x) from (by
          unfold nb081_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0045 x) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_040 A) from (by
          unfold nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042 A) 0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from
        (by
          unfold nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from
                                      (by
                                        unfold nb081_alpha_dummy_046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0048 A)
                                                0)))) (show x ≠ (nb081_alpha_dummy_047 x) from
                                      (by
                                        unfold nb081_alpha_dummy_047;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb081_support_mem_0049 x)
                                                0)))) (TAlphaVar.there (show
                                        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_044 A)
                                        from (by
                                          unfold nb081_alpha_dummy_044;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0046 A) 0))))
                                      (show x ≠ (nb081_alpha_dummy_045 x) from (by
                                          unfold nb081_alpha_dummy_045;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb081_support_mem_0047 x) 0))))
                                      (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_042 A) from (by
          unfold nb081_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0044 A) 0)))) (show x ≠ (nb081_alpha_dummy_043 x) from (by
          unfold nb081_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0045 x) 0)))) (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_040 A) from (by
          unfold nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042 A) 0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from
        (by
          unfold nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043 x y) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_x_y (TAlphaVar.here _ _ _))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from (by
          unfold nb081_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081_alpha_dummy_047 x) from (by
          unfold nb081_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_054 A) from (by
          unfold nb081_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_055 x) from (by
          unfold nb081_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from (by
          unfold nb081_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081_alpha_dummy_047 x) from (by
          unfold nb081_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_054 A) from (by
          unfold nb081_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_055 x) from (by
          unfold nb081_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_058 A) from (by
          unfold nb081_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081_alpha_dummy_059 y) from (by
          unfold nb081_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_056 A) from (by
          unfold nb081_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_057 y) from (by
          unfold nb081_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_058 A) from (by
          unfold nb081_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081_alpha_dummy_059 y) from (by
          unfold nb081_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_056 A) from (by
          unfold nb081_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_057 y) from (by
          unfold nb081_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from (by
          unfold nb081_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081_alpha_dummy_047 x) from (by
          unfold nb081_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_054 A) from (by
          unfold nb081_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_055 x) from (by
          unfold nb081_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_000 A) ≠ (nb081_alpha_dummy_046 A) from (by
          unfold nb081_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0048 A)
                  0)))) (show x ≠ (nb081_alpha_dummy_047 x) from (by
          unfold nb081_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0049 x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_054 A) from (by
          unfold nb081_alpha_dummy_054;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0056
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_055 x) from (by
          unfold nb081_alpha_dummy_055;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0057
                    x)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0054
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0055
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0052
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0053
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0050
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0051
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_000 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0042
                    A)
                  0)))) (show x ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0043
                    x y)
                  0)))) (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_058 A) from (by
          unfold nb081_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081_alpha_dummy_059 y) from (by
          unfold nb081_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_056 A) from (by
          unfold nb081_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_057 y) from (by
          unfold nb081_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb081_alpha_dummy_001 A) ≠ (nb081_alpha_dummy_058 A) from (by
          unfold nb081_alpha_dummy_058;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0068 A)
                  0)))) (show y ≠ (nb081_alpha_dummy_059 y) from (by
          unfold nb081_alpha_dummy_059;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0069 y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_056 A) from (by
          unfold nb081_alpha_dummy_056;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0066
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_057 y) from (by
          unfold nb081_alpha_dummy_057;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0067
                    y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_052 A) from (by
          unfold nb081_alpha_dummy_052;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0064
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_053 x y) from (by
          unfold nb081_alpha_dummy_053;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0065
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_050 A) from (by
          unfold
            nb081_alpha_dummy_050;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0062
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_051 x y) from (by
          unfold
            nb081_alpha_dummy_051;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0063
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_048 A) from (by
          unfold
            nb081_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0060
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_049 x y) from (by
          unfold
            nb081_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0061
                    x y)
                  0)))) (TAlphaVar.there (show (nb081_alpha_dummy_001 A) ≠
        (nb081_alpha_dummy_040 A) from (by
          unfold
            nb081_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0058
                    A)
                  0)))) (show y ≠ (nb081_alpha_dummy_041 x y) from (by
          unfold
            nb081_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb081_support_mem_0059
                    x y)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))))))
        (TAlphaClass.refl_of_reflOn
          [((nb081_alpha_dummy_001 A), y), ((nb081_alpha_dummy_000 A), x),
            ((nb081_alpha_dummy_002 A), (nb081_alpha_dummy_003 x y A))]
          A (nb081_focused_refl_0000 x y A dv_A_x dv_A_y)))))

@[expose]
noncomputable def nominal_df_kqrel (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_ckqrel A) (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) A))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.neg (nb081_split_alpha_0001 x y A dv_A_x dv_A_y dv_x_y)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
