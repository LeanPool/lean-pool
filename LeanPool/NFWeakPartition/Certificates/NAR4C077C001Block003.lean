/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C077C001Part009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C077C001Part010`. -/


section

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
noncomputable def nb077_split_alpha_0000 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_025 F I))
          (Class.cab (nb077_alpha_dummy_019 F I)
            (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_025 F I))
            (Class.cab (nb077_alpha_dummy_019 F I)
              (syn_wrex (nb077_alpha_dummy_020 F I) (Class.cv (nb077_alpha_dummy_016 F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_019 F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_026 x F I))
          (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
              (Class.cv (nb077_alpha_dummy_018 x F I))
              (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_026 x F I))
            (Class.cab (nb077_alpha_dummy_021 x F I) (syn_wrex (nb077_alpha_dummy_022 x F I)
                (Class.cv (nb077_alpha_dummy_018 x F I))
                (Wff.classEq (Class.cv (nb077_alpha_dummy_021 x F I))
                  (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
                      unfold nb077_alpha_dummy_020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
                  (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
                      unfold nb077_alpha_dummy_022;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
                        unfold nb077_alpha_dummy_019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
                    (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from (by
                        unfold nb077_alpha_dummy_021;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                    (TAlphaVar.there
                      (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_025 F I) from (by
                          unfold nb077_alpha_dummy_025;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0014 F I) 0))))
                      (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_026 x F I) from
                        (by
                          unfold nb077_alpha_dummy_026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0015 x F I) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_023 F I) from (by
                            unfold nb077_alpha_dummy_023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0011 F I) 0)))) (show
                          (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_024 x F I) from (by
                            unfold nb077_alpha_dummy_024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0013 x F I) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
                      ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_027 F I) from
                            (by
                              unfold nb077_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_029 x F I) from
                            (by
                              unfold nb077_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I) from (by
                                unfold nb077_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_030 x F I) from
                              (by
                                unfold nb077_alpha_dummy_030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from
        (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_037 x F I) from (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F
        I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034
        F I) ≠ (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_025 F I),
                                      (nb077_alpha_dummy_026 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077_alpha_dummy_029 x F I) ≠
                                      (nb077_alpha_dummy_032 x F I) from (by
                                      unfold nb077_alpha_dummy_032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_025 F I),
                                      (nb077_alpha_dummy_026 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_020 F I) from (by
                        unfold nb077_alpha_dummy_020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0010 F I) 1))))
                    (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_022 x F I) from (by
                        unfold nb077_alpha_dummy_022;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb077_support_mem_0012 x F I) 1))))
                    (TAlphaVar.there
                      (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_019 F I) from (by
                          unfold nb077_alpha_dummy_019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0010 F I) 0))))
                      (show (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_021 x F I) from
                        (by
                          unfold nb077_alpha_dummy_021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb077_support_mem_0012 x F I) 0))))
                      (TAlphaVar.there
                        (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_025 F I) from (by
                            unfold nb077_alpha_dummy_025;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0014 F I) 0)))) (show
                          (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_026 x F I) from (by
                            unfold nb077_alpha_dummy_026;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb077_support_mem_0015 x F I) 0))))
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_016 F I) ≠ (nb077_alpha_dummy_023 F I) from
                            (by
                              unfold nb077_alpha_dummy_023;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0011 F I) 0)))) (show
                            (nb077_alpha_dummy_018 x F I) ≠ (nb077_alpha_dummy_024 x F I) from
                            (by
                              unfold nb077_alpha_dummy_024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0013 x F I) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb077_alpha_dummy_016 F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_015 F I))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb077_alpha_dummy_018 x F I))).fv ∪
                        ((Class.cv (nb077_alpha_dummy_017 x F I))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_027 F I) from (by
                                unfold nb077_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                              (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_029 x F I) from
                              (by
                                unfold nb077_alpha_dummy_029;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        0)))) (TAlphaVar.there (show
                                (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I) from
                                (by
                                  unfold nb077_alpha_dummy_028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0016 F I)
                                          1)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                  (nb077_alpha_dummy_030 x F I) from (by
                                  unfold nb077_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  1)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_037 x F I) from
        (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F
                    I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_025 F I), (nb077_alpha_dummy_026 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F
        I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034
        F I) ≠ (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
                                          unfold nb077_alpha_dummy_031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0018 F I) 0)))) (show
                                        (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
                                          unfold nb077_alpha_dummy_032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0019 x F I) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_031 F I),
                                        (nb077_alpha_dummy_032 x F I)),
                                      ((nb077_alpha_dummy_027 F I),
                                        (nb077_alpha_dummy_029 x F I)),
                                      ((nb077_alpha_dummy_028 F I),
                                        (nb077_alpha_dummy_030 x F I)),
                                      ((nb077_alpha_dummy_020 F I),
                                        (nb077_alpha_dummy_022 x F I)),
                                      ((nb077_alpha_dummy_019 F I),
                                        (nb077_alpha_dummy_021 x F I)),
                                      ((nb077_alpha_dummy_025 F I),
                                        (nb077_alpha_dummy_026 x F I)),
                                      ((nb077_alpha_dummy_023 F I),
                                        (nb077_alpha_dummy_024 x F I)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
                                          unfold nb077_alpha_dummy_031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0018 F I) 0)))) (show
                                        (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_032 x F I) from (by
                                          unfold nb077_alpha_dummy_032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb077_support_mem_0019 x F I) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb077_alpha_dummy_031 F I),
                                        (nb077_alpha_dummy_032 x F I)),
                                      ((nb077_alpha_dummy_027 F I),
                                        (nb077_alpha_dummy_029 x F I)),
                                      ((nb077_alpha_dummy_028 F I),
                                        (nb077_alpha_dummy_030 x F I)),
                                      ((nb077_alpha_dummy_020 F I),
                                        (nb077_alpha_dummy_022 x F I)),
                                      ((nb077_alpha_dummy_019 F I),
                                        (nb077_alpha_dummy_021 x F I)),
                                      ((nb077_alpha_dummy_025 F I),
                                        (nb077_alpha_dummy_026 x F I)),
                                      ((nb077_alpha_dummy_023 F I),
                                        (nb077_alpha_dummy_024 x F I)),
                                      ((nb077_alpha_dummy_016 F I),
                                        (nb077_alpha_dummy_018 x F I)),
                                      ((nb077_alpha_dummy_015 F I),
                                        (nb077_alpha_dummy_017 x F I)),
                                      ((nb077_alpha_dummy_013 F I),
                                        (nb077_alpha_dummy_014 x F I)),
                                      ((nb077_alpha_dummy_011 F I),
                                        (nb077_alpha_dummy_012 x F I)),
                                      ((nb077_alpha_dummy_001 F I),
                                        (nb077_alpha_dummy_002 x F I)),
                                      ((nb077_alpha_dummy_004 F I),
                                        (nb077_alpha_dummy_006 x F I)),
                                      ((nb077_alpha_dummy_003 F I),
                                        (nb077_alpha_dummy_005 x F I))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C077C001Part011`. -/


section

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
noncomputable def nb077_split_alpha_0001 (x : Var) (F : Class) (I : Class) :
    TAlphaWff
      [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_051 F I))
          (syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_020 F I))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_051 F I))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb077_alpha_dummy_052 x F I))
          (syn_ccompl (syn_cphi (Class.cv (nb077_alpha_dummy_022 x F I))))) (Wff.neg
          (Wff.classMem (Class.cv (nb077_alpha_dummy_052 x F I))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_027 F I) from
                            (by
                              unfold nb077_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_029 x F I) from
                            (by
                              unfold nb077_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I) from (by
                                unfold nb077_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_030 x F I) from
                              (by
                                unfold nb077_alpha_dummy_030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.there (show
                                (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_053 F I) from
                                (by
                                  unfold nb077_alpha_dummy_053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0046 F I)
                                          0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                  (nb077_alpha_dummy_054 x F I) from (by
                                  unfold nb077_alpha_dummy_054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0047 x F I)
                                          0)))) (TAlphaVar.there (show
                                  (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_051 F I) from
                                  (by
                                    unfold nb077_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0044 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_052 x F I) from (by
                                    unfold nb077_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0045 x F I)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from
        (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_037 x F I) from (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F
        I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034
        F I) ≠ (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_053 F I),
                                      (nb077_alpha_dummy_054 x F I)),
                                    ((nb077_alpha_dummy_051 F I),
                                      (nb077_alpha_dummy_052 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_049 F I),
                                      (nb077_alpha_dummy_050 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077_alpha_dummy_029 x F I) ≠
                                      (nb077_alpha_dummy_032 x F I) from (by
                                      unfold nb077_alpha_dummy_032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_053 F I),
                                      (nb077_alpha_dummy_054 x F I)),
                                    ((nb077_alpha_dummy_051 F I),
                                      (nb077_alpha_dummy_052 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_049 F I),
                                      (nb077_alpha_dummy_050 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_027 F I) from
                            (by
                              unfold nb077_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0016 F I) 0)))) (show
                            (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_029 x F I) from
                            (by
                              unfold nb077_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb077_support_mem_0017 x F I) 0))))
                          (TAlphaVar.there (show
                              (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_028 F I) from (by
                                unfold nb077_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0016 F I) 1)))) (show
                              (nb077_alpha_dummy_022 x F I) ≠ (nb077_alpha_dummy_030 x F I) from
                              (by
                                unfold nb077_alpha_dummy_030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb077_support_mem_0017 x F I)
                                        1)))) (TAlphaVar.there (show
                                (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_053 F I) from
                                (by
                                  unfold nb077_alpha_dummy_053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0046 F I)
                                          0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                  (nb077_alpha_dummy_054 x F I) from (by
                                  unfold nb077_alpha_dummy_054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb077_support_mem_0047 x F I)
                                          0)))) (TAlphaVar.there (show
                                  (nb077_alpha_dummy_020 F I) ≠ (nb077_alpha_dummy_051 F I) from
                                  (by
                                    unfold nb077_alpha_dummy_051;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0044 F I)
                                            0)))) (show (nb077_alpha_dummy_022 x F I) ≠
                                    (nb077_alpha_dummy_052 x F I) from (by
                                    unfold nb077_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb077_support_mem_0045 x F I)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_020 F I))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb077_alpha_dummy_022 x F I))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_034 F I) from
        (by
          unfold nb077_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I) 1)))) (show (nb077_alpha_dummy_029 x F I) ≠
        (nb077_alpha_dummy_037 x F I) from (by
          unfold nb077_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  1)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_033 F I) from (by
          unfold nb077_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0020 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_036 x F I) from
        (by
          unfold nb077_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0021 x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_027 F I) ≠
        (nb077_alpha_dummy_031 F I) from (by
          unfold nb077_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0018 F I)
                  0)))) (show (nb077_alpha_dummy_029 x F I) ≠ (nb077_alpha_dummy_032 x F I) from
        (by
          unfold nb077_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0019 x F I)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0024
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0025
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0022
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0023
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠ (nb077_alpha_dummy_041 F I) from
        (by
          unfold
            nb077_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0028
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_042 x F I) from
        (by
          unfold
            nb077_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0029
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_039 F I) from (by
          unfold
            nb077_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0026
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_040 x F I) from
        (by
          unfold
            nb077_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0027
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb077_alpha_dummy_035 F I), (nb077_alpha_dummy_038 x F I)),
        ((nb077_alpha_dummy_034 F I), (nb077_alpha_dummy_037 x F I)),
        ((nb077_alpha_dummy_033 F I), (nb077_alpha_dummy_036 x F I)),
        ((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
        ((nb077_alpha_dummy_027 F I), (nb077_alpha_dummy_029 x F I)),
        ((nb077_alpha_dummy_028 F I), (nb077_alpha_dummy_030 x F I)),
        ((nb077_alpha_dummy_053 F I), (nb077_alpha_dummy_054 x F I)),
        ((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
        ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
        ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
        ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
        ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
        ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
        ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
        ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
        ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
        ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
        ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
        ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027 F I))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb077_alpha_dummy_029 x F
        I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_027 F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_034
        F I) ≠ (nb077_alpha_dummy_045 F I) from (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠ (nb077_alpha_dummy_045 F I) from
        (by
          unfold
            nb077_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0032
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_046 x F I) from
        (by
          unfold
            nb077_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0033
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_034 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0030
                    F I)
                  0)))) (show (nb077_alpha_dummy_037 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0031
                    x F I)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb077_alpha_dummy_027
        F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb077_alpha_dummy_029 x F I))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb077_alpha_dummy_035
        F I) ≠ (nb077_alpha_dummy_047 F I) from (by
          unfold
            nb077_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0036
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_048 x F I) from
        (by
          unfold
            nb077_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0037
                    x F I)
                  0)))) (TAlphaVar.there (show (nb077_alpha_dummy_035 F I) ≠
        (nb077_alpha_dummy_043 F I) from (by
          unfold
            nb077_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0034
                    F I)
                  0)))) (show (nb077_alpha_dummy_038 x F I) ≠ (nb077_alpha_dummy_044 x F I) from
        (by
          unfold
            nb077_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb077_support_mem_0035
                    x F I)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_053 F I),
                                      (nb077_alpha_dummy_054 x F I)),
                                    ((nb077_alpha_dummy_051 F I),
                                      (nb077_alpha_dummy_052 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_049 F I),
                                      (nb077_alpha_dummy_050 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                    from (by
                                      unfold nb077_alpha_dummy_031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb077_support_mem_0018 F I)
                                              0)))) (show (nb077_alpha_dummy_029 x F I) ≠
                                      (nb077_alpha_dummy_032 x F I) from (by
                                      unfold nb077_alpha_dummy_032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb077_support_mem_0019 x F I) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb077_alpha_dummy_027 F I) ≠ (nb077_alpha_dummy_031 F I)
                                      from (by
                                        unfold nb077_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0018 F I) 0)))) (show
                                      (nb077_alpha_dummy_029 x F I) ≠
                                        (nb077_alpha_dummy_032 x F I) from (by
                                        unfold nb077_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb077_support_mem_0019 x F I) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb077_alpha_dummy_031 F I), (nb077_alpha_dummy_032 x F I)),
                                    ((nb077_alpha_dummy_027 F I),
                                      (nb077_alpha_dummy_029 x F I)),
                                    ((nb077_alpha_dummy_028 F I),
                                      (nb077_alpha_dummy_030 x F I)),
                                    ((nb077_alpha_dummy_053 F I),
                                      (nb077_alpha_dummy_054 x F I)),
                                    ((nb077_alpha_dummy_051 F I),
                                      (nb077_alpha_dummy_052 x F I)),
                                    ((nb077_alpha_dummy_020 F I),
                                      (nb077_alpha_dummy_022 x F I)),
                                    ((nb077_alpha_dummy_019 F I),
                                      (nb077_alpha_dummy_021 x F I)),
                                    ((nb077_alpha_dummy_049 F I),
                                      (nb077_alpha_dummy_050 x F I)),
                                    ((nb077_alpha_dummy_023 F I),
                                      (nb077_alpha_dummy_024 x F I)),
                                    ((nb077_alpha_dummy_016 F I),
                                      (nb077_alpha_dummy_018 x F I)),
                                    ((nb077_alpha_dummy_015 F I),
                                      (nb077_alpha_dummy_017 x F I)),
                                    ((nb077_alpha_dummy_013 F I),
                                      (nb077_alpha_dummy_014 x F I)),
                                    ((nb077_alpha_dummy_011 F I),
                                      (nb077_alpha_dummy_012 x F I)),
                                    ((nb077_alpha_dummy_001 F I),
                                      (nb077_alpha_dummy_002 x F I)),
                                    ((nb077_alpha_dummy_004 F I),
                                      (nb077_alpha_dummy_006 x F I)),
                                    ((nb077_alpha_dummy_003 F I),
                                      (nb077_alpha_dummy_005 x F I))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed
          [((nb077_alpha_dummy_051 F I), (nb077_alpha_dummy_052 x F I)),
            ((nb077_alpha_dummy_020 F I), (nb077_alpha_dummy_022 x F I)),
            ((nb077_alpha_dummy_019 F I), (nb077_alpha_dummy_021 x F I)),
            ((nb077_alpha_dummy_049 F I), (nb077_alpha_dummy_050 x F I)),
            ((nb077_alpha_dummy_023 F I), (nb077_alpha_dummy_024 x F I)),
            ((nb077_alpha_dummy_016 F I), (nb077_alpha_dummy_018 x F I)),
            ((nb077_alpha_dummy_015 F I), (nb077_alpha_dummy_017 x F I)),
            ((nb077_alpha_dummy_013 F I), (nb077_alpha_dummy_014 x F I)),
            ((nb077_alpha_dummy_011 F I), (nb077_alpha_dummy_012 x F I)),
            ((nb077_alpha_dummy_001 F I), (nb077_alpha_dummy_002 x F I)),
            ((nb077_alpha_dummy_004 F I), (nb077_alpha_dummy_006 x F I)),
            ((nb077_alpha_dummy_003 F I), (nb077_alpha_dummy_005 x F I))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

theorem nb077_compact_fv_empty_0064 (F : Class) (I : Class) :
    (nb077_alpha_dummy_060 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0065 (x : Var) :
    (nb077_alpha_dummy_063 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0066 (F : Class) (I : Class) :
    (nb077_alpha_dummy_059 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0067 (x : Var) :
    (nb077_alpha_dummy_062 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0068 (F : Class) (I : Class) :
    (nb077_alpha_dummy_065 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0069 (x : Var) :
    (nb077_alpha_dummy_066 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0070 (F : Class) (I : Class) :
    (nb077_alpha_dummy_057 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0071 (x : Var) (F : Class) :
    (nb077_alpha_dummy_058 x F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0072 (F : Class) (I : Class) :
    (nb077_alpha_dummy_055 F I) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb077_compact_fv_empty_0073 (x : Var) (F : Class) :
    (nb077_alpha_dummy_056 x F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
