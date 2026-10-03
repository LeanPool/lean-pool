/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C095M3Part008Block001


/-! NF weak partition development: NAR4H5C095M3Part008. -/


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
noncomputable def nb095_split_alpha_0000 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_025 D R S_cls E), (nb095_alpha_dummy_026 f)),
        ((nb095_alpha_dummy_023 D R S_cls E), (nb095_alpha_dummy_024 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_025 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_025 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_019 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_020 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_011 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_019 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_020 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_026 f))
          (Class.cab (nb095_alpha_dummy_021 f)
            (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_026 f))
            (Class.cab (nb095_alpha_dummy_021 f)
              (syn_wrex (nb095_alpha_dummy_022 f) (Class.cv (nb095_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_021 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_022 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                      (nb095_alpha_dummy_020 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_020;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_022 f) from (by
                      unfold nb095_alpha_dummy_022;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0006 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                        (nb095_alpha_dummy_019 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_019;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_021 f) from (by
                        unfold nb095_alpha_dummy_021;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0006 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                          (nb095_alpha_dummy_025 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_025;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0008 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_026 f) from (by
                          unfold nb095_alpha_dummy_026;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0009 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                            (nb095_alpha_dummy_023 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_023;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0005 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_024 f) from (by
                            unfold nb095_alpha_dummy_024;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0007 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv
                                  (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_020 D R S_cls E) ≠
                              (nb095_alpha_dummy_027 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_027;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0010 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_022 f) ≠ (nb095_alpha_dummy_029 f) from (by
                              unfold nb095_alpha_dummy_029;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0011 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_020 D R S_cls E) ≠
                                (nb095_alpha_dummy_028 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_028;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0010 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_022 f) ≠ (nb095_alpha_dummy_030 f) from (by
                                unfold nb095_alpha_dummy_030;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0011 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_022 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_027 D R S_cls E) ≠
        (nb095_alpha_dummy_034 D R S_cls E) from (by
          unfold nb095_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_037 f) from (by
          unfold nb095_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_027 D R S_cls E) ≠ (nb095_alpha_dummy_033 D R S_cls E) from (by
          unfold nb095_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_036 f) from (by
          unfold nb095_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_027 D R S_cls E) ≠ (nb095_alpha_dummy_031 D R S_cls E) from (by
          unfold nb095_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0012 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from (by
          unfold nb095_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_035 D R S_cls E), (nb095_alpha_dummy_038 f)),
        ((nb095_alpha_dummy_034 D R S_cls E), (nb095_alpha_dummy_037 f)),
        ((nb095_alpha_dummy_033 D R S_cls E), (nb095_alpha_dummy_036 f)),
        ((nb095_alpha_dummy_031 D R S_cls E), (nb095_alpha_dummy_032 f)),
        ((nb095_alpha_dummy_027 D R S_cls E), (nb095_alpha_dummy_029 f)),
        ((nb095_alpha_dummy_028 D R S_cls E), (nb095_alpha_dummy_030 f)),
        ((nb095_alpha_dummy_020 D R S_cls E), (nb095_alpha_dummy_022 f)),
        ((nb095_alpha_dummy_019 D R S_cls E), (nb095_alpha_dummy_021 f)),
        ((nb095_alpha_dummy_025 D R S_cls E), (nb095_alpha_dummy_026 f)),
        ((nb095_alpha_dummy_023 D R S_cls E), (nb095_alpha_dummy_024 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_034
        D R S_cls E) ≠ (nb095_alpha_dummy_041 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_035 D R S_cls E), (nb095_alpha_dummy_038 f)),
        ((nb095_alpha_dummy_034 D R S_cls E), (nb095_alpha_dummy_037 f)),
        ((nb095_alpha_dummy_033 D R S_cls E), (nb095_alpha_dummy_036 f)),
        ((nb095_alpha_dummy_031 D R S_cls E), (nb095_alpha_dummy_032 f)),
        ((nb095_alpha_dummy_027 D R S_cls E), (nb095_alpha_dummy_029 f)),
        ((nb095_alpha_dummy_028 D R S_cls E), (nb095_alpha_dummy_030 f)),
        ((nb095_alpha_dummy_020 D R S_cls E), (nb095_alpha_dummy_022 f)),
        ((nb095_alpha_dummy_019 D R S_cls E), (nb095_alpha_dummy_021 f)),
        ((nb095_alpha_dummy_025 D R S_cls E), (nb095_alpha_dummy_026 f)),
        ((nb095_alpha_dummy_023 D R S_cls E), (nb095_alpha_dummy_024 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_045
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_046 f) from (by
          unfold
            nb095_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_045
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_046 f) from (by
          unfold
            nb095_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_035
        D R S_cls E) ≠ (nb095_alpha_dummy_047 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_048 f) from (by
          unfold
            nb095_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_035
        D R S_cls E) ≠ (nb095_alpha_dummy_047 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_048 f) from (by
          unfold
            nb095_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_027 D R S_cls E) ≠
                                        (nb095_alpha_dummy_031 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from
                                      (by
                                        unfold nb095_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_031 D R S_cls E),
                                      (nb095_alpha_dummy_032 f)),
                                    ((nb095_alpha_dummy_027 D R S_cls E),
                                      (nb095_alpha_dummy_029 f)),
                                    ((nb095_alpha_dummy_028 D R S_cls E),
                                      (nb095_alpha_dummy_030 f)),
                                    ((nb095_alpha_dummy_020 D R S_cls E),
                                      (nb095_alpha_dummy_022 f)),
                                    ((nb095_alpha_dummy_019 D R S_cls E),
                                      (nb095_alpha_dummy_021 f)),
                                    ((nb095_alpha_dummy_025 D R S_cls E),
                                      (nb095_alpha_dummy_026 f)),
                                    ((nb095_alpha_dummy_023 D R S_cls E),
                                      (nb095_alpha_dummy_024 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_027 D R S_cls E) ≠
                                      (nb095_alpha_dummy_031 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_031;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from
                                    (by
                                      unfold nb095_alpha_dummy_032;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0013 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_027 D R S_cls E) ≠
                                        (nb095_alpha_dummy_031 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from
                                      (by
                                        unfold nb095_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_031 D R S_cls E),
                                      (nb095_alpha_dummy_032 f)),
                                    ((nb095_alpha_dummy_027 D R S_cls E),
                                      (nb095_alpha_dummy_029 f)),
                                    ((nb095_alpha_dummy_028 D R S_cls E),
                                      (nb095_alpha_dummy_030 f)),
                                    ((nb095_alpha_dummy_020 D R S_cls E),
                                      (nb095_alpha_dummy_022 f)),
                                    ((nb095_alpha_dummy_019 D R S_cls E),
                                      (nb095_alpha_dummy_021 f)),
                                    ((nb095_alpha_dummy_025 D R S_cls E),
                                      (nb095_alpha_dummy_026 f)),
                                    ((nb095_alpha_dummy_023 D R S_cls E),
                                      (nb095_alpha_dummy_024 f)),
                                    ((nb095_alpha_dummy_012 D R S_cls E),
                                      (nb095_alpha_dummy_015 f)),
                                    ((nb095_alpha_dummy_011 D R S_cls E),
                                      (nb095_alpha_dummy_014 f)),
                                    ((nb095_alpha_dummy_017 D R S_cls E),
                                      (nb095_alpha_dummy_018 f)),
                                    ((nb095_alpha_dummy_009 D R S_cls E),
                                      (nb095_alpha_dummy_010 f)),
                                    ((nb095_alpha_dummy_007 D R S_cls E),
                                      (nb095_alpha_dummy_008 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                        (nb095_alpha_dummy_020 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_020;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_022 f) from (by
                        unfold nb095_alpha_dummy_022;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0006 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                          (nb095_alpha_dummy_019 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_019;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0004 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_021 f) from (by
                          unfold nb095_alpha_dummy_021;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0006 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                            (nb095_alpha_dummy_025 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_025;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0008 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_026 f) from (by
                            unfold nb095_alpha_dummy_026;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0009 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_011 D R S_cls E) ≠
                              (nb095_alpha_dummy_023 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_023;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0005 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_014 f) ≠ (nb095_alpha_dummy_024 f) from (by
                              unfold nb095_alpha_dummy_024;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0007 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_011 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_012 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_014 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_015 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_020 D R S_cls E) ≠
                                (nb095_alpha_dummy_027 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_027;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0010 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_022 f) ≠ (nb095_alpha_dummy_029 f) from (by
                                unfold nb095_alpha_dummy_029;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0011 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_020 D R S_cls E) ≠
                                  (nb095_alpha_dummy_028 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_028;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0010 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_022 f) ≠ (nb095_alpha_dummy_030 f) from
                                (by
                                  unfold nb095_alpha_dummy_030;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0011 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_020 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_022 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_027 D R S_cls E) ≠ (nb095_alpha_dummy_034 D R S_cls E) from (by
          unfold nb095_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_037 f) from (by
          unfold nb095_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_027 D R S_cls E) ≠ (nb095_alpha_dummy_033 D R S_cls E) from (by
          unfold nb095_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0014 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_036 f) from (by
          unfold nb095_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0015 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_027 D R S_cls E) ≠
        (nb095_alpha_dummy_031 D R S_cls E) from (by
          unfold nb095_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0012 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from (by
          unfold nb095_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0013 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_035 D R S_cls E), (nb095_alpha_dummy_038 f)),
        ((nb095_alpha_dummy_034 D R S_cls E), (nb095_alpha_dummy_037 f)),
        ((nb095_alpha_dummy_033 D R S_cls E), (nb095_alpha_dummy_036 f)),
        ((nb095_alpha_dummy_031 D R S_cls E), (nb095_alpha_dummy_032 f)),
        ((nb095_alpha_dummy_027 D R S_cls E), (nb095_alpha_dummy_029 f)),
        ((nb095_alpha_dummy_028 D R S_cls E), (nb095_alpha_dummy_030 f)),
        ((nb095_alpha_dummy_020 D R S_cls E), (nb095_alpha_dummy_022 f)),
        ((nb095_alpha_dummy_019 D R S_cls E), (nb095_alpha_dummy_021 f)),
        ((nb095_alpha_dummy_025 D R S_cls E), (nb095_alpha_dummy_026 f)),
        ((nb095_alpha_dummy_023 D R S_cls E), (nb095_alpha_dummy_024 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_034
        D R S_cls E) ≠ (nb095_alpha_dummy_041 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0018
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0019
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0016
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0017
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠ (nb095_alpha_dummy_041
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0022
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_042 f) from (by
          unfold
            nb095_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0023
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_039 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_039;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0020
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_040 f) from (by
          unfold
            nb095_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0021
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_035 D R S_cls E), (nb095_alpha_dummy_038 f)),
        ((nb095_alpha_dummy_034 D R S_cls E), (nb095_alpha_dummy_037 f)),
        ((nb095_alpha_dummy_033 D R S_cls E), (nb095_alpha_dummy_036 f)),
        ((nb095_alpha_dummy_031 D R S_cls E), (nb095_alpha_dummy_032 f)),
        ((nb095_alpha_dummy_027 D R S_cls E), (nb095_alpha_dummy_029 f)),
        ((nb095_alpha_dummy_028 D R S_cls E), (nb095_alpha_dummy_030 f)),
        ((nb095_alpha_dummy_020 D R S_cls E), (nb095_alpha_dummy_022 f)),
        ((nb095_alpha_dummy_019 D R S_cls E), (nb095_alpha_dummy_021 f)),
        ((nb095_alpha_dummy_025 D R S_cls E), (nb095_alpha_dummy_026 f)),
        ((nb095_alpha_dummy_023 D R S_cls E), (nb095_alpha_dummy_024 f)),
        ((nb095_alpha_dummy_012 D R S_cls E), (nb095_alpha_dummy_015 f)),
        ((nb095_alpha_dummy_011 D R S_cls E), (nb095_alpha_dummy_014 f)),
        ((nb095_alpha_dummy_017 D R S_cls E), (nb095_alpha_dummy_018 f)),
        ((nb095_alpha_dummy_009 D R S_cls E), (nb095_alpha_dummy_010 f)),
        ((nb095_alpha_dummy_007 D R S_cls E), (nb095_alpha_dummy_008 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_027 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_045
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_046 f) from (by
          unfold
            nb095_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠ (nb095_alpha_dummy_045
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_045;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0026
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_046 f) from (by
          unfold
            nb095_alpha_dummy_046;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0027
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_034 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0024
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_037 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0025
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_027
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_029 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_035
        D R S_cls E) ≠ (nb095_alpha_dummy_047 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_048 f) from (by
          unfold
            nb095_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_035
        D R S_cls E) ≠ (nb095_alpha_dummy_047 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_047;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0030
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_048 f) from (by
          unfold
            nb095_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0031
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_035 D R S_cls E) ≠
        (nb095_alpha_dummy_043 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0028
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_038 f) ≠ (nb095_alpha_dummy_044 f) from (by
          unfold
            nb095_alpha_dummy_044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0029
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_027 D R S_cls E) ≠
        (nb095_alpha_dummy_031 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0012 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_029 f) ≠
        (nb095_alpha_dummy_032 f) from (by
                                          unfold nb095_alpha_dummy_032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_031 D R S_cls E),
                                        (nb095_alpha_dummy_032 f)),
                                      ((nb095_alpha_dummy_027 D R S_cls E),
                                        (nb095_alpha_dummy_029 f)),
                                      ((nb095_alpha_dummy_028 D R S_cls E),
                                        (nb095_alpha_dummy_030 f)),
                                      ((nb095_alpha_dummy_020 D R S_cls E),
                                        (nb095_alpha_dummy_022 f)),
                                      ((nb095_alpha_dummy_019 D R S_cls E),
                                        (nb095_alpha_dummy_021 f)),
                                      ((nb095_alpha_dummy_025 D R S_cls E),
                                        (nb095_alpha_dummy_026 f)),
                                      ((nb095_alpha_dummy_023 D R S_cls E),
                                        (nb095_alpha_dummy_024 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_027 D R S_cls E) ≠
                                        (nb095_alpha_dummy_031 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_031;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0012 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_029 f) ≠ (nb095_alpha_dummy_032 f) from
                                      (by
                                        unfold nb095_alpha_dummy_032;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0013 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_027 D R S_cls E) ≠
        (nb095_alpha_dummy_031 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_031;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0012 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_029 f) ≠
        (nb095_alpha_dummy_032 f) from (by
                                          unfold nb095_alpha_dummy_032;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0013 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_031 D R S_cls E),
                                        (nb095_alpha_dummy_032 f)),
                                      ((nb095_alpha_dummy_027 D R S_cls E),
                                        (nb095_alpha_dummy_029 f)),
                                      ((nb095_alpha_dummy_028 D R S_cls E),
                                        (nb095_alpha_dummy_030 f)),
                                      ((nb095_alpha_dummy_020 D R S_cls E),
                                        (nb095_alpha_dummy_022 f)),
                                      ((nb095_alpha_dummy_019 D R S_cls E),
                                        (nb095_alpha_dummy_021 f)),
                                      ((nb095_alpha_dummy_025 D R S_cls E),
                                        (nb095_alpha_dummy_026 f)),
                                      ((nb095_alpha_dummy_023 D R S_cls E),
                                        (nb095_alpha_dummy_024 f)),
                                      ((nb095_alpha_dummy_012 D R S_cls E),
                                        (nb095_alpha_dummy_015 f)),
                                      ((nb095_alpha_dummy_011 D R S_cls E),
                                        (nb095_alpha_dummy_014 f)),
                                      ((nb095_alpha_dummy_017 D R S_cls E),
                                        (nb095_alpha_dummy_018 f)),
                                      ((nb095_alpha_dummy_009 D R S_cls E),
                                        (nb095_alpha_dummy_010 f)),
                                      ((nb095_alpha_dummy_007 D R S_cls E),
                                        (nb095_alpha_dummy_008 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
