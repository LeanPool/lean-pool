/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C097M3Part001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4H5C097M3Part001`. -/


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
noncomputable def nb097_split_alpha_0000 (C : Class) (k : Var) (m : Var) (F : Class) :
    TAlphaWff
      [((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_009 C F))
          (Class.cv (nb097_alpha_dummy_000 C F))) (Wff.neg
          (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
            (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_011 k m)) (Class.cv k)) (Wff.neg
          (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
            (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_009 C F) from
            (by
              unfold nb097_alpha_dummy_009;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
          (show k ≠ (nb097_alpha_dummy_011 k m) from (by
              unfold nb097_alpha_dummy_011;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
          (TAlphaVar.there (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_008 C F) from
              (by
                unfold nb097_alpha_dummy_008;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
            (show k ≠ (nb097_alpha_dummy_010 k m) from (by
                unfold nb097_alpha_dummy_010;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
            (TAlphaVar.there
              (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_038 C F) from (by
                  unfold nb097_alpha_dummy_038;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0032 C F) 0))))
              (show k ≠ (nb097_alpha_dummy_039 k m) from (by
                  unfold nb097_alpha_dummy_039;
                  with_reducible
                    exact
                      (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0033 k m) 0))))
              (TAlphaVar.there
                (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_012 C F) from (by
                    unfold nb097_alpha_dummy_012;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0029 C F) 0))))
                (show k ≠ (nb097_alpha_dummy_013 k m) from (by
                    unfold nb097_alpha_dummy_013;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0031 k m) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
                ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (by decide))
            (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_016 C F)
                                      from (by
                                        unfold nb097_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 0)))) (show
                                      (nb097_alpha_dummy_011 k m) ≠ (nb097_alpha_dummy_018 k m)
                                      from (by
                                        unfold nb097_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 0))))
                                    (TAlphaVar.there (show (nb097_alpha_dummy_009 C F) ≠
        (nb097_alpha_dummy_017 C F) from (by
                                          unfold nb097_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0006 C F) 1)))) (show
                                        (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_019 k m) from (by
                                          unfold nb097_alpha_dummy_019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0007 k m) 1))))
                                      (TAlphaVar.there (show (nb097_alpha_dummy_009 C F) ≠
        (nb097_alpha_dummy_042 C F) from (by
          unfold nb097_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0036 C F) 0)))) (show (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_043 k m) from (by
          unfold nb097_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0037 k m) 0)))) (TAlphaVar.there (show
        (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_040 C F) from (by
          unfold nb097_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0034 C F) 0)))) (show (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_041 k m) from (by
          unfold nb097_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0035 k m) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_023 C F) from
        (by
          unfold nb097_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  1)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_026 k m) from (by
          unfold nb097_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  1)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_022 C F) from (by
          unfold nb097_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_025 k m) from (by
          unfold nb097_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold
            nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold
            nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023
        C F) ≠ (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠ (nb097_alpha_dummy_036 C F) from
        (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_036 C F) from (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from
        (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_016 C F)
                                      from (by
                                        unfold nb097_alpha_dummy_016;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 0)))) (show
                                      (nb097_alpha_dummy_011 k m) ≠ (nb097_alpha_dummy_018 k m)
                                      from (by
                                        unfold nb097_alpha_dummy_018;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 0))))
                                    (TAlphaVar.there (show (nb097_alpha_dummy_009 C F) ≠
        (nb097_alpha_dummy_017 C F) from (by
                                          unfold nb097_alpha_dummy_017;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0006 C F) 1)))) (show
                                        (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_019 k m) from (by
                                          unfold nb097_alpha_dummy_019;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb097_support_mem_0007 k m) 1))))
                                      (TAlphaVar.there (show (nb097_alpha_dummy_009 C F) ≠
        (nb097_alpha_dummy_042 C F) from (by
          unfold nb097_alpha_dummy_042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0036 C F) 0)))) (show (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_043 k m) from (by
          unfold nb097_alpha_dummy_043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0037 k m) 0)))) (TAlphaVar.there (show
        (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_040 C F) from (by
          unfold nb097_alpha_dummy_040;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0034 C F) 0)))) (show (nb097_alpha_dummy_011 k m) ≠
        (nb097_alpha_dummy_041 k m) from (by
          unfold nb097_alpha_dummy_041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0035 k m) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_023 C F) from
        (by
          unfold nb097_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  1)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_026 k m) from (by
          unfold nb097_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  1)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_022 C F) from (by
          unfold nb097_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_025 k m) from (by
          unfold nb097_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold
            nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold
            nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023
        C F) ≠ (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠ (nb097_alpha_dummy_036 C F) from
        (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_036 C F) from (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from
        (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_042 C F), (nb097_alpha_dummy_043 k m)),
        ((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb097_alpha_dummy_040 C F), (nb097_alpha_dummy_041 k m)),
                    ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
                    ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
                    ((nb097_alpha_dummy_038 C F), (nb097_alpha_dummy_039 k m)),
                    ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
                    ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
                    ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
                    ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
                    ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
                  (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4H5C097M3Part002`. -/


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
noncomputable def nb097_split_alpha_0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_k_m : k ≠ m) :
    TAlphaWff
      [((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_012 C F)) (syn_ccompl
            (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb097_alpha_dummy_012 C F)) (syn_ccompl
              (Class.cab (nb097_alpha_dummy_008 C F) (syn_wrex (nb097_alpha_dummy_009 C F)
                  (Class.cv (nb097_alpha_dummy_000 C F))
                  (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                    (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb097_alpha_dummy_013 k m)) (syn_ccompl
            (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb097_alpha_dummy_013 k m)) (syn_ccompl
              (Class.cab (nb097_alpha_dummy_010 k m)
                (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
                  (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                    (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_009 C F) from
                            (by
                              unfold nb097_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
                          (show m ≠ (nb097_alpha_dummy_011 k m) from (by
                              unfold nb097_alpha_dummy_011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
                          (TAlphaVar.there (show
                              (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
                                unfold nb097_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
                            (show m ≠ (nb097_alpha_dummy_010 k m) from (by
                                unfold nb097_alpha_dummy_010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
                            (TAlphaVar.there (show
                                (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_014 C F) from
                                (by
                                  unfold nb097_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0004 C F)
                                          0)))) (show m ≠ (nb097_alpha_dummy_015 k m) from (by
                                  unfold nb097_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0005 k m)
                                          0)))) (TAlphaVar.there (show
                                  (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_012 C F) from
                                  (by
                                    unfold nb097_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0001 C F)
                                            0)))) (show m ≠ (nb097_alpha_dummy_013 k m) from (by
                                    unfold nb097_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0003 k m)
                                            0)))) (TAlphaVar.there
                                  (freshVar_injective ((F).fv ∪ (C).fv) (by decide))
                                  (Ne.symm dv_k_m) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
                              ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (by decide))
                          (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_016 C F)
                                    from (by
                                      unfold nb097_alpha_dummy_016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0006 C F)
                                              0)))) (show (nb097_alpha_dummy_011 k m) ≠
                                      (nb097_alpha_dummy_018 k m) from (by
                                      unfold nb097_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0007 k m)
                                              0)))) (TAlphaVar.there (show
                                      (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_017 C F)
                                      from (by
                                        unfold nb097_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 1)))) (show
                                      (nb097_alpha_dummy_011 k m) ≠ (nb097_alpha_dummy_019 k m)
                                      from (by
                                        unfold nb097_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_023 C F) from (by
          unfold nb097_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010 C
                    F)
                  1)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_026 k m) from (by
          unfold nb097_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011 k
                    m)
                  1)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_022 C F) from (by
          unfold nb097_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_025 k m) from (by
          unfold nb097_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023
        C F) ≠ (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠ (nb097_alpha_dummy_036 C F) from
        (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_036 C F) from (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_009 C F) from
                            (by
                              unfold nb097_alpha_dummy_009;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
                          (show m ≠ (nb097_alpha_dummy_011 k m) from (by
                              unfold nb097_alpha_dummy_011;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
                          (TAlphaVar.there (show
                              (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
                                unfold nb097_alpha_dummy_008;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
                            (show m ≠ (nb097_alpha_dummy_010 k m) from (by
                                unfold nb097_alpha_dummy_010;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
                            (TAlphaVar.there (show
                                (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_014 C F) from
                                (by
                                  unfold nb097_alpha_dummy_014;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0004 C F)
                                          0)))) (show m ≠ (nb097_alpha_dummy_015 k m) from (by
                                  unfold nb097_alpha_dummy_015;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb097_support_mem_0005 k m)
                                          0)))) (TAlphaVar.there (show
                                  (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_012 C F) from
                                  (by
                                    unfold nb097_alpha_dummy_012;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0001 C F)
                                            0)))) (show m ≠ (nb097_alpha_dummy_013 k m) from (by
                                    unfold nb097_alpha_dummy_013;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb097_support_mem_0003 k m)
                                            0)))) (TAlphaVar.there
                                  (freshVar_injective ((F).fv ∪ (C).fv) (by decide))
                                  (Ne.symm dv_k_m) (TAlphaVar.here _ _ _))))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
                              ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (by decide))
                          (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_016 C F)
                                    from (by
                                      unfold nb097_alpha_dummy_016;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0006 C F)
                                              0)))) (show (nb097_alpha_dummy_011 k m) ≠
                                      (nb097_alpha_dummy_018 k m) from (by
                                      unfold nb097_alpha_dummy_018;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb097_support_mem_0007 k m)
                                              0)))) (TAlphaVar.there (show
                                      (nb097_alpha_dummy_009 C F) ≠ (nb097_alpha_dummy_017 C F)
                                      from (by
                                        unfold nb097_alpha_dummy_017;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0006 C F) 1)))) (show
                                      (nb097_alpha_dummy_011 k m) ≠ (nb097_alpha_dummy_019 k m)
                                      from (by
                                        unfold nb097_alpha_dummy_019;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb097_support_mem_0007 k m) 1))))
                                    (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_023 C F) from (by
          unfold nb097_alpha_dummy_023;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010 C
                    F)
                  1)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_026 k m) from (by
          unfold nb097_alpha_dummy_026;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011 k
                    m)
                  1)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_022 C F) from (by
          unfold nb097_alpha_dummy_022;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0010
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_025 k m) from (by
          unfold nb097_alpha_dummy_025;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0011
                    k m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008
                    C F)
                  0)))) (show (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009
                    k m)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_030 C F) from
        (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0014
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0015
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0012
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0013
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_030 C F) from (by
          unfold
            nb097_alpha_dummy_030;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0018
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_031 k m) from (by
          unfold
            nb097_alpha_dummy_031;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0019
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_028 C F) from (by
          unfold
            nb097_alpha_dummy_028;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0016
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_029 k m) from (by
          unfold
            nb097_alpha_dummy_029;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0017
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_024 C F), (nb097_alpha_dummy_027 k m)),
        ((nb097_alpha_dummy_023 C F), (nb097_alpha_dummy_026 k m)),
        ((nb097_alpha_dummy_022 C F), (nb097_alpha_dummy_025 k m)),
        ((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _
        _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_023
        C F) ≠ (nb097_alpha_dummy_034 C F) from (by
          unfold
            nb097_alpha_dummy_034;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0022
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_035 k m) from (by
          unfold
            nb097_alpha_dummy_035;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0023
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_023 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0020
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0021
                    k
                    m)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb097_alpha_dummy_016
        C F))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠ (nb097_alpha_dummy_036 C F) from
        (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb097_alpha_dummy_024
        C F) ≠ (nb097_alpha_dummy_036 C F) from (by
          unfold
            nb097_alpha_dummy_036;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0026
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_037 k m) from (by
          unfold
            nb097_alpha_dummy_037;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0027
                    k
                    m)
                  0)))) (TAlphaVar.there (show (nb097_alpha_dummy_024 C F) ≠
        (nb097_alpha_dummy_032 C F) from (by
          unfold
            nb097_alpha_dummy_032;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0024
                    C
                    F)
                  0)))) (show (nb097_alpha_dummy_027 k m) ≠ (nb097_alpha_dummy_033 k m) from (by
          unfold
            nb097_alpha_dummy_033;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0025
                    k
                    m)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb097_alpha_dummy_016 C F) ≠
        (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_020 C F) from (by
          unfold nb097_alpha_dummy_020;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0008 C F) 0)))) (show (nb097_alpha_dummy_018 k m) ≠
        (nb097_alpha_dummy_021 k m) from (by
          unfold nb097_alpha_dummy_021;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb097_support_mem_0009 k m) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed
        [((nb097_alpha_dummy_020 C F), (nb097_alpha_dummy_021 k m)),
        ((nb097_alpha_dummy_016 C F), (nb097_alpha_dummy_018 k m)),
        ((nb097_alpha_dummy_017 C F), (nb097_alpha_dummy_019 k m)),
        ((nb097_alpha_dummy_009 C F), (nb097_alpha_dummy_011 k m)),
        ((nb097_alpha_dummy_008 C F), (nb097_alpha_dummy_010 k m)),
        ((nb097_alpha_dummy_014 C F), (nb097_alpha_dummy_015 k m)),
        ((nb097_alpha_dummy_012 C F), (nb097_alpha_dummy_013 k m)),
        ((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb097_split_alpha_0000 C k m F)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb097_split_alpha_0000 C k m F)))))))))))

theorem nb097_wpp_notmem_0132 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_clec] using (nb097_compact_fv_empty_0020 C F)

theorem nb097_wpp_notmem_0133 (k : Var) : k ∉ ((syn_clec)).fv := by
  simpa only [fv_syn_clec] using (nb097_compact_fv_empty_0021 k)

theorem nb097_wpp_notmem_0134 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_clec] using (nb097_compact_fv_empty_0022 C F)

theorem nb097_wpp_notmem_0135 (m : Var) : m ∉ ((syn_clec)).fv := by
  simpa only [fv_syn_clec] using (nb097_compact_fv_empty_0023 m)

theorem nb097_wpp_notmem_0136 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_clec] using (nb097_compact_fv_empty_0024 C F)

theorem nb097_wpp_notmem_0137 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_clec] using
    (nb097_compact_fv_empty_0025 C k m F)

theorem nb097_wpp_notmem_0138 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_clec] using (nb097_compact_fv_empty_0026 C F)

theorem nb097_wpp_notmem_0139 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_007 C k m F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_clec] using
    (nb097_compact_fv_empty_0027 C k m F)

theorem nb097_wpp_notmem_0140 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_clec] using (nb097_compact_fv_empty_0028 C F)

theorem nb097_wpp_notmem_0141 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_006 C k m F) ∉ ((syn_clec)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_clec] using
    (nb097_compact_fv_empty_0029 C k m F)

theorem nb097_compact_envfresh_0009 (C : Class) (k : Var) (m : Var) (F : Class) :
    TEnvFresh
      [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_clec)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0132 C F)
      (nb097_wpp_notmem_0133 k)
      (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0134 C F)
        (nb097_wpp_notmem_0135 m)
        (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F)
          (nb097_wpp_notmem_0136 C F) (nb097_wpp_notmem_0137 C k m F)
          (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F)
            (nb097_wpp_notmem_0138 C F) (nb097_wpp_notmem_0139 C k m F)
            (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F)
              (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0140 C F)
              (nb097_wpp_notmem_0141 C k m F) (TEnvFresh.nil ((syn_clec)).fv))))))

@[expose]
noncomputable def nb097_wpp_refl_0009 (C : Class) (k : Var) (m : Var) (F : Class) :
    TReflOn
      [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_clec)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0009 C k m F)

@[expose]
noncomputable def nominal_df_wppgamma (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv)
    (dv_k_m : k ≠ m) :
    Nominal.NPrf
      (.classEq (syn_cwppgamma F C) (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
                        (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                            (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F))
                              (syn_cwppcand F C))
                            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                                (Class.cv (nb097_alpha_dummy_000 C F))))))
                        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) (by decide))
                (freshVar_injective (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq
                        (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                            (syn_wral k (syn_cwppcand F C)
                              (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
                        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_001 C F), m),
                            ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
                            ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
                            ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
                          (syn_cwppcand F C) (nb097_wpp_refl_0000 C k m F dv_C_m dv_F_m)))
                      (TAlphaWff.all (TAlphaWff.imp
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_000 C F), k),
                                ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F),
                                  (nb097_alpha_dummy_003 C k m F)),
                                ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
                                ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
                              (syn_cwppcand F C)
                              (nb097_wpp_refl_0001 C k m F dv_C_k dv_C_m dv_F_k dv_F_m)))
                          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb097_split_alpha_0001 C k m F dv_k_m))))
                            (TAlphaClass.refl_of_reflOn [((nb097_alpha_dummy_000 C F), k),
                                ((nb097_alpha_dummy_001 C F), m), ((nb097_alpha_dummy_002 C F),
                                  (nb097_alpha_dummy_003 C k m F)),
                                ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
                                ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
                              (syn_clec) (nb097_wpp_refl_0009 C k m F))))))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb097_alpha_dummy_002 C F) ≠ (nb097_alpha_dummy_044 C F) from
                            (by
                              unfold nb097_alpha_dummy_044;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0038 C F) 0)))) (show
                            (nb097_alpha_dummy_003 C k m F) ≠ (nb097_alpha_dummy_045 C k m F)
                            from (by
                              unfold nb097_alpha_dummy_045;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb097_support_mem_0039 C k m F)
                                      0)))) (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
