/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C093M3Part002Block001


/-! NF weak partition development: NAR4H5C093M3Part002. -/


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
noncomputable def nb093_split_alpha_0000 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
        ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)),
        ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_009 A))
          (Class.cv (nb093_alpha_dummy_000 A))) (Wff.neg
          (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
            (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_011 r d)) (Class.cv d)) (Wff.neg
          (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
            (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_009 A) from (by
              unfold nb093_alpha_dummy_009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 1))))
          (show d ≠ (nb093_alpha_dummy_011 r d) from (by
              unfold nb093_alpha_dummy_011;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 1))))
          (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_008 A) from (by
                unfold nb093_alpha_dummy_008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0032 A) 0))))
            (show d ≠ (nb093_alpha_dummy_010 r d) from (by
                unfold nb093_alpha_dummy_010;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0034 r d) 0))))
            (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_038 A) from
                (by
                  unfold nb093_alpha_dummy_038;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0036 A) 0))))
              (show d ≠ (nb093_alpha_dummy_039 r d) from (by
                  unfold nb093_alpha_dummy_039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0037 r d) 0))))
              (TAlphaVar.there (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_012 A) from
                  (by
                    unfold nb093_alpha_dummy_012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0033 A) 0))))
                (show d ≠ (nb093_alpha_dummy_013 r d) from (by
                    unfold nb093_alpha_dummy_013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0035 r d) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
                ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_016 A) from
                                      (by
                                        unfold nb093_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                0)))) (show (nb093_alpha_dummy_011 r d) ≠
                                        (nb093_alpha_dummy_018 r d) from (by
                                        unfold nb093_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_009 A) ≠
        (nb093_alpha_dummy_017 A) from (by
                                          unfold nb093_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0010 A) 1)))) (show
                                        (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_019 r d) from (by
                                          unfold nb093_alpha_dummy_019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0011 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_009 A) ≠
        (nb093_alpha_dummy_042 A) from (by
          unfold nb093_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0040 A) 0)))) (show (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_043 r d) from (by
          unfold nb093_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0041 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_040 A) from (by
          unfold nb093_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0038 A) 0)))) (show (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_041 r d) from (by
          unfold nb093_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0039 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_023 A) from (by
          unfold nb093_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  1)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_026 r d) from (by
          unfold nb093_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_022 A) from (by
          unfold nb093_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_025 r d) from (by
          unfold nb093_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold
            nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_021 r d) from (by
          unfold
            nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018
        r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023
        A) ≠ (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_016 A) from
                                      (by
                                        unfold nb093_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                0)))) (show (nb093_alpha_dummy_011 r d) ≠
                                        (nb093_alpha_dummy_018 r d) from (by
                                        unfold nb093_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_009 A) ≠
        (nb093_alpha_dummy_017 A) from (by
                                          unfold nb093_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0010 A) 1)))) (show
                                        (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_019 r d) from (by
                                          unfold nb093_alpha_dummy_019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0011 r d) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_009 A) ≠
        (nb093_alpha_dummy_042 A) from (by
          unfold nb093_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0040 A) 0)))) (show (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_043 r d) from (by
          unfold nb093_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0041 r d) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_040 A) from (by
          unfold nb093_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0038 A) 0)))) (show (nb093_alpha_dummy_011 r d) ≠
        (nb093_alpha_dummy_041 r d) from (by
          unfold nb093_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0039 r d) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_023 A) from (by
          unfold nb093_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  1)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_026 r d) from (by
          unfold nb093_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_022 A) from (by
          unfold nb093_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_025 r d) from (by
          unfold nb093_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold
            nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_021 r d) from (by
          unfold
            nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018
        r d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023
        A) ≠ (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_042 A), (nb093_alpha_dummy_043 r d)), ((nb093_alpha_dummy_040 A),
        (nb093_alpha_dummy_041 r d)), ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
        ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_038 A),
        (nb093_alpha_dummy_039 r d)), ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb093_alpha_dummy_040 A), (nb093_alpha_dummy_041 r d)),
                    ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)),
                    ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
                    ((nb093_alpha_dummy_038 A), (nb093_alpha_dummy_039 r d)),
                    ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
                    ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                    ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                    ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb093_split_alpha_0001 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_012 A)) (syn_ccompl
            (Class.cab (nb093_alpha_dummy_008 A)
              (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_012 A)) (syn_ccompl
              (Class.cab (nb093_alpha_dummy_008 A)
                (syn_wrex (nb093_alpha_dummy_009 A) (Class.cv (nb093_alpha_dummy_000 A))
                  (Wff.classEq (Class.cv (nb093_alpha_dummy_008 A))
                    (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_009 A)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_013 r d)) (syn_ccompl
            (Class.cab (nb093_alpha_dummy_010 r d)
              (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv r)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_013 r d)) (syn_ccompl
              (Class.cab (nb093_alpha_dummy_010 r d)
                (syn_wrex (nb093_alpha_dummy_011 r d) (Class.cv d)
                  (Wff.classEq (Class.cv (nb093_alpha_dummy_010 r d))
                    (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_011 r d)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_009 A) from (by
                              unfold nb093_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
                          (show r ≠ (nb093_alpha_dummy_011 r d) from (by
                              unfold nb093_alpha_dummy_011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_008 A) from (by
                                unfold nb093_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
                            (show r ≠ (nb093_alpha_dummy_010 r d) from (by
                                unfold nb093_alpha_dummy_010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_014 A) from
                                (by
                                  unfold nb093_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0008 A) 0))))
                              (show r ≠ (nb093_alpha_dummy_015 r d) from (by
                                  unfold nb093_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0009 r d)
                                          0)))) (TAlphaVar.there (show
                                  (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_012 A) from (by
                                    unfold nb093_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0005 A)
                                            0)))) (show r ≠ (nb093_alpha_dummy_013 r d) from (by
                                    unfold nb093_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0007 r d)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
                              ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide))
                          (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_016 A) from
                                    (by
                                      unfold nb093_alpha_dummy_016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0010 A)
                                              0)))) (show (nb093_alpha_dummy_011 r d) ≠
                                      (nb093_alpha_dummy_018 r d) from (by
                                      unfold nb093_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0011 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_017 A) from
                                      (by
                                        unfold nb093_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                1)))) (show (nb093_alpha_dummy_011 r d) ≠
                                        (nb093_alpha_dummy_019 r d) from (by
                                        unfold nb093_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_023 A) from (by
          unfold nb093_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014 A)
                  1)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_026 r d) from (by
          unfold nb093_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015 r
                    d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_022 A) from (by
          unfold nb093_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_025 r d) from (by
          unfold nb093_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A),
        (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)),
        ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A),
        (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)),
        ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r
        d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023
        A) ≠ (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_020 A),
        (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)),
        ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A),
        (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
        ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A),
        (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_020 A),
        (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)),
        ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A),
        (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
        ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A),
        (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_009 A) from (by
                              unfold nb093_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0004 A) 1))))
                          (show r ≠ (nb093_alpha_dummy_011 r d) from (by
                              unfold nb093_alpha_dummy_011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0006 r d) 1))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_008 A) from (by
                                unfold nb093_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0004 A) 0))))
                            (show r ≠ (nb093_alpha_dummy_010 r d) from (by
                                unfold nb093_alpha_dummy_010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0006 r d) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_014 A) from
                                (by
                                  unfold nb093_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0008 A) 0))))
                              (show r ≠ (nb093_alpha_dummy_015 r d) from (by
                                  unfold nb093_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0009 r d)
                                          0)))) (TAlphaVar.there (show
                                  (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_012 A) from (by
                                    unfold nb093_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0005 A)
                                            0)))) (show r ≠ (nb093_alpha_dummy_013 r d) from (by
                                    unfold nb093_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0007 r d)
                                            0))))
                                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                  (Ne.symm dv_d_r) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb093_alpha_dummy_001 A))).fv ∪
                              ((Class.cv (nb093_alpha_dummy_000 A))).fv) (by decide))
                          (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv d)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_016 A) from
                                    (by
                                      unfold nb093_alpha_dummy_016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0010 A)
                                              0)))) (show (nb093_alpha_dummy_011 r d) ≠
                                      (nb093_alpha_dummy_018 r d) from (by
                                      unfold nb093_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0011 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_009 A) ≠ (nb093_alpha_dummy_017 A) from
                                      (by
                                        unfold nb093_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0010 A)
                                                1)))) (show (nb093_alpha_dummy_011 r d) ≠
                                        (nb093_alpha_dummy_019 r d) from (by
                                        unfold nb093_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0011 r d) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb093_alpha_dummy_009 A))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb093_alpha_dummy_011 r d))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_023 A) from (by
          unfold nb093_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014 A)
                  1)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_026 r d) from (by
          unfold nb093_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015 r
                    d)
                  1)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_022 A) from (by
          unfold nb093_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0014
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_025 r d) from (by
          unfold nb093_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0015
                    r d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012
                    A)
                  0)))) (show (nb093_alpha_dummy_018 r d) ≠ (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013
                    r d)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A),
        (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)),
        ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0018
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0019
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0016
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0017
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_030 A) from (by
          unfold
            nb093_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0022
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_031 r d) from (by
          unfold
            nb093_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0023
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_028 A) from (by
          unfold
            nb093_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0020
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_029 r d) from (by
          unfold
            nb093_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0021
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_024 A), (nb093_alpha_dummy_027 r d)), ((nb093_alpha_dummy_023 A),
        (nb093_alpha_dummy_026 r d)), ((nb093_alpha_dummy_022 A), (nb093_alpha_dummy_025 r d)),
        ((nb093_alpha_dummy_020 A), (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A),
        (nb093_alpha_dummy_018 r d)), ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)),
        ((nb093_alpha_dummy_009 A), (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A),
        (nb093_alpha_dummy_010 r d)), ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)),
        ((nb093_alpha_dummy_012 A), (nb093_alpha_dummy_013 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r
        d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r
        d))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_016 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_023
        A) ≠ (nb093_alpha_dummy_034 A) from (by
          unfold
            nb093_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0026
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_035 r d) from (by
          unfold
            nb093_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0027
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_023 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0024
                    A)
                  0)))) (show (nb093_alpha_dummy_026 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0025
                    r
                    d)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_016
        A))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_018 r d))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_024
        A) ≠ (nb093_alpha_dummy_036 A) from (by
          unfold
            nb093_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0030
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_037 r d) from (by
          unfold
            nb093_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0031
                    r
                    d)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_024 A) ≠
        (nb093_alpha_dummy_032 A) from (by
          unfold
            nb093_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0028
                    A)
                  0)))) (show (nb093_alpha_dummy_027 r d) ≠ (nb093_alpha_dummy_033 r d) from (by
          unfold
            nb093_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0029
                    r
                    d)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_020 A),
        (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)),
        ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A),
        (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
        ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A),
        (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb093_alpha_dummy_016 A) ≠
        (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_016 A) ≠ (nb093_alpha_dummy_020 A) from (by
          unfold nb093_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0012 A) 0)))) (show (nb093_alpha_dummy_018 r d) ≠
        (nb093_alpha_dummy_021 r d) from (by
          unfold nb093_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0013 r d) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_020 A),
        (nb093_alpha_dummy_021 r d)), ((nb093_alpha_dummy_016 A), (nb093_alpha_dummy_018 r d)),
        ((nb093_alpha_dummy_017 A), (nb093_alpha_dummy_019 r d)), ((nb093_alpha_dummy_009 A),
        (nb093_alpha_dummy_011 r d)), ((nb093_alpha_dummy_008 A), (nb093_alpha_dummy_010 r d)),
        ((nb093_alpha_dummy_014 A), (nb093_alpha_dummy_015 r d)), ((nb093_alpha_dummy_012 A),
        (nb093_alpha_dummy_013 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb093_split_alpha_0000 A r d)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb093_split_alpha_0000 A r d)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
