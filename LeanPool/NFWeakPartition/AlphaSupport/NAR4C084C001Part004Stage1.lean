/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C084C001Part003

/-! NF weak partition development: NAR4C084C001Part004. -/


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
noncomputable def nb084_split_alpha_0001 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) :
    TAlphaWff
      [((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      (Wff.imp (Wff.classMem (Class.cv (nb084_alpha_dummy_010 A B R))
          (Class.cv (nb084_alpha_dummy_004 A B R))) (Wff.neg
          (Wff.classEq (Class.cv (nb084_alpha_dummy_009 A B R))
            (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_010 A B R))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb084_alpha_dummy_012 x y A R))
          (Class.cv (nb084_alpha_dummy_006 x y A R))) (Wff.neg
          (Wff.classEq (Class.cv (nb084_alpha_dummy_011 x y A R))
            (syn_cun (syn_cphi (Class.cv (nb084_alpha_dummy_012 x y A R)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_010 A B R) from (by
              unfold nb084_alpha_dummy_010;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 1))))
          (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_012 x y A R) from (by
              unfold nb084_alpha_dummy_012;
              with_reducible
                exact
                  (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 1))))
          (TAlphaVar.there
            (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_009 A B R) from (by
                unfold nb084_alpha_dummy_009;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0036 A B R) 0))))
            (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_011 x y A R) from (by
                unfold nb084_alpha_dummy_011;
                with_reducible
                  exact
                    (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0038 x y A R) 0))))
            (TAlphaVar.there
              (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_039 A B R) from (by
                  unfold nb084_alpha_dummy_039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb084_support_mem_0040 A B R) 0))))
              (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_040 x y A R) from (by
                  unfold nb084_alpha_dummy_040;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb084_support_mem_0041 x y A R) 0)))) (TAlphaVar.there
                (show (nb084_alpha_dummy_004 A B R) ≠ (nb084_alpha_dummy_013 A B R) from (by
                    unfold nb084_alpha_dummy_013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb084_support_mem_0037 A B R) 0))))
                (show (nb084_alpha_dummy_006 x y A R) ≠ (nb084_alpha_dummy_014 x y A R) from (by
                    unfold nb084_alpha_dummy_014;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb084_support_mem_0039 x y A R) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_003 A B R))).fv ∪
                ((Class.cv (nb084_alpha_dummy_004 A B R))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb084_alpha_dummy_005 x y A R))).fv ∪
                ((Class.cv (nb084_alpha_dummy_006 x y A R))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084_alpha_dummy_010 A B R) ≠
                                        (nb084_alpha_dummy_017 A B R) from (by
                                        unfold nb084_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0014 A B R) 0)))) (show
                                      (nb084_alpha_dummy_012 x y A R) ≠
                                        (nb084_alpha_dummy_019 x y A R) from (by
                                        unfold nb084_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0015 x y A R) 0))))
                                    (TAlphaVar.there (show (nb084_alpha_dummy_010 A B R) ≠
        (nb084_alpha_dummy_018 A B R) from (by
                                          unfold nb084_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0014 A B R) 1)))) (show
                                        (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_020 x y A R) from (by
                                          unfold nb084_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0015 x y A R) 1))))
                                      (TAlphaVar.there (show (nb084_alpha_dummy_010 A B R) ≠
        (nb084_alpha_dummy_043 A B R) from (by
          unfold nb084_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0044 A B R) 0)))) (show (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_044 x y A R) from (by
          unfold nb084_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0045 x y A R) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_010 A B R) ≠ (nb084_alpha_dummy_041 A B R) from (by
          unfold nb084_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0042 A B R) 0)))) (show (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_042 x y A R) from (by
          unfold nb084_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0043 x y A R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb084_alpha_dummy_010 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠ (nb084_alpha_dummy_024 A B R)
        from (by
          unfold nb084_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  1)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_027 x y A R)
        from (by
          unfold nb084_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_023 A B R) from (by
          unfold nb084_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_026 x y A R)
        from (by
          unfold nb084_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold
            nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016
                    A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)),
        ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)),
        ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)),
        ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠ (nb084_alpha_dummy_031 A B R)
        from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)),
        ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)),
        ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)),
        ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019
        x y A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠ (nb084_alpha_dummy_035 A B R)
        from (by
          unfold
            nb084_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_036 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_024
        A B R) ≠ (nb084_alpha_dummy_035 A B R) from (by
          unfold
            nb084_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_036 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠ (nb084_alpha_dummy_037 A B R)
        from (by
          unfold
            nb084_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_038 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_037 A B R) from (by
          unfold
            nb084_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_038 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠ (nb084_alpha_dummy_021 A B R)
        from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb084_alpha_dummy_010 A B R) ≠
                                        (nb084_alpha_dummy_017 A B R) from (by
                                        unfold nb084_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0014 A B R) 0)))) (show
                                      (nb084_alpha_dummy_012 x y A R) ≠
                                        (nb084_alpha_dummy_019 x y A R) from (by
                                        unfold nb084_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb084_support_mem_0015 x y A R) 0))))
                                    (TAlphaVar.there (show (nb084_alpha_dummy_010 A B R) ≠
        (nb084_alpha_dummy_018 A B R) from (by
                                          unfold nb084_alpha_dummy_018;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0014 A B R) 1)))) (show
                                        (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_020 x y A R) from (by
                                          unfold nb084_alpha_dummy_020;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb084_support_mem_0015 x y A R) 1))))
                                      (TAlphaVar.there (show (nb084_alpha_dummy_010 A B R) ≠
        (nb084_alpha_dummy_043 A B R) from (by
          unfold nb084_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0044 A B R) 0)))) (show (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_044 x y A R) from (by
          unfold nb084_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0045 x y A R) 0)))) (TAlphaVar.there (show
        (nb084_alpha_dummy_010 A B R) ≠ (nb084_alpha_dummy_041 A B R) from (by
          unfold nb084_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0042 A B R) 0)))) (show (nb084_alpha_dummy_012 x y A R) ≠
        (nb084_alpha_dummy_042 x y A R) from (by
          unfold nb084_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0043 x y A R)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                  (TAlphaVar.there (freshVar_injective
                                      (((Class.cv (nb084_alpha_dummy_010 A B R))).fv)
                                      (by decide)) (freshVar_injective
                                      (((Class.cv (nb084_alpha_dummy_012 x y A R))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠ (nb084_alpha_dummy_024 A B R)
        from (by
          unfold nb084_alpha_dummy_024;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  1)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_027 x y A R)
        from (by
          unfold nb084_alpha_dummy_027;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  1)))) (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_023 A B R) from (by
          unfold nb084_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0018
                    A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_026 x y A R)
        from (by
          unfold nb084_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0019
                    x y A R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold
            nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016
                    A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017
                    x y A R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)),
        ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)),
        ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)),
        ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠ (nb084_alpha_dummy_031 A B R)
        from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0022
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0023
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0020
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0021
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_031 A B R) from (by
          unfold
            nb084_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0026
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_032 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0027
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_029 A B R) from (by
          unfold
            nb084_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0024
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_030 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0025
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_025 A B R), (nb084_alpha_dummy_028 x y A R)),
        ((nb084_alpha_dummy_024 A B R), (nb084_alpha_dummy_027 x y A R)),
        ((nb084_alpha_dummy_023 A B R), (nb084_alpha_dummy_026 x y A R)),
        ((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb084_alpha_dummy_017 A B R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017 A B R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019
        x y A R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠ (nb084_alpha_dummy_035 A B R)
        from (by
          unfold
            nb084_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_036 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_024
        A B R) ≠ (nb084_alpha_dummy_035 A B R) from (by
          unfold
            nb084_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0030
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_036 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0031
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_024 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0028
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_027 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0029
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb084_alpha_dummy_017
        A B R))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb084_alpha_dummy_019 x y A R))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠ (nb084_alpha_dummy_037 A B R)
        from (by
          unfold
            nb084_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_038 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_025
        A B R) ≠ (nb084_alpha_dummy_037 A B R) from (by
          unfold
            nb084_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0034
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_038 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_038;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0035
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.there (show (nb084_alpha_dummy_025 A B R) ≠
        (nb084_alpha_dummy_033 A B R) from (by
          unfold
            nb084_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0032
                    A
                    B
                    R)
                  0)))) (show (nb084_alpha_dummy_028 x y A R) ≠ (nb084_alpha_dummy_034 x y A R)
        from (by
          unfold
            nb084_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0033
                    x
                    y
                    A
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠ (nb084_alpha_dummy_021 A B R)
        from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb084_alpha_dummy_017 A B R) ≠
        (nb084_alpha_dummy_021 A B R) from (by
          unfold nb084_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0016 A B R)
                  0)))) (show (nb084_alpha_dummy_019 x y A R) ≠ (nb084_alpha_dummy_022 x y A R)
        from (by
          unfold nb084_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb084_support_mem_0017 x y A R)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb084_alpha_dummy_021 A B R), (nb084_alpha_dummy_022 x y A R)),
        ((nb084_alpha_dummy_017 A B R), (nb084_alpha_dummy_019 x y A R)),
        ((nb084_alpha_dummy_018 A B R), (nb084_alpha_dummy_020 x y A R)),
        ((nb084_alpha_dummy_043 A B R), (nb084_alpha_dummy_044 x y A R)),
        ((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
        ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
        ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
        ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
        ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
        ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb084_alpha_dummy_041 A B R), (nb084_alpha_dummy_042 x y A R)),
                    ((nb084_alpha_dummy_010 A B R), (nb084_alpha_dummy_012 x y A R)),
                    ((nb084_alpha_dummy_009 A B R), (nb084_alpha_dummy_011 x y A R)),
                    ((nb084_alpha_dummy_039 A B R), (nb084_alpha_dummy_040 x y A R)),
                    ((nb084_alpha_dummy_013 A B R), (nb084_alpha_dummy_014 x y A R)),
                    ((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
                    ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
                    ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
                    ((nb084_alpha_dummy_000 A B R), d)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb084_focused_notmem_0010 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_004 A B R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
          ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
        1 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0011 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_006 x y A R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0012 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        ((R).fv ∪ (A).fv ∪ ((Class.cv (nb084_alpha_dummy_001 A B R))).fv ∪
          ((Class.cv (nb084_alpha_dummy_002 A B R))).fv)
        0 ∉
      R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0013 (x : Var) (y : Var) (A : Class) (R : Class) :
    (nb084_alpha_dummy_005 x y A R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ ((Class.cv x)).fv ∪ ((Class.cv y)).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb084_focused_notmem_0014 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_002 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 2 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_focused_notmem_0015 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_001 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 1 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_focused_notmem_0016 (A : Class) (B : Class) (R : Class) :
    (nb084_alpha_dummy_000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb084_compact_envfresh_0012 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (d : Var) (dv_R_d : d ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) :
    TEnvFresh
      [((nb084_alpha_dummy_004 A B R), (nb084_alpha_dummy_006 x y A R)),
        ((nb084_alpha_dummy_003 A B R), (nb084_alpha_dummy_005 x y A R)),
        ((nb084_alpha_dummy_002 A B R), y), ((nb084_alpha_dummy_001 A B R), x),
        ((nb084_alpha_dummy_000 A B R), d)]
      R.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb084_alpha_dummy_004 A B R) (nb084_alpha_dummy_006 x y A R)
      (nb084_focused_notmem_0010 A B R) (nb084_focused_notmem_0011 x y A R)
      (TEnvFresh.consFresh (nb084_alpha_dummy_003 A B R) (nb084_alpha_dummy_005 x y A R)
        (nb084_focused_notmem_0012 A B R) (nb084_focused_notmem_0013 x y A R)
        (TEnvFresh.consFresh (nb084_alpha_dummy_002 A B R) y
          (nb084_focused_notmem_0014 A B R) dv_R_y
          (TEnvFresh.consFresh (nb084_alpha_dummy_001 A B R) x
            (nb084_focused_notmem_0015 A B R) dv_R_x
            (TEnvFresh.consFresh (nb084_alpha_dummy_000 A B R) d
              (nb084_focused_notmem_0016 A B R) dv_R_d (TEnvFresh.nil R.fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
