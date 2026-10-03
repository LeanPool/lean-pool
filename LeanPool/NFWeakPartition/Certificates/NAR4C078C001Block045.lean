/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C078C001Part135Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part135`. -/


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
noncomputable def nb078_wpp_refl_0372 (x : Var) (y : Var) (h : Var) :
    TReflOn
      [((nb078_alpha_dummy_765), (nb078_alpha_dummy_766 h)),
        ((nb078_alpha_dummy_763), (nb078_alpha_dummy_764 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0372 x y h)

@[expose]
noncomputable def nb078_split_alpha_0113 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_781))
          (Class.cab (nb078_alpha_dummy_775)
            (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                (syn_cphi (Class.cv (nb078_alpha_dummy_776))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_781)) (Class.cab (nb078_alpha_dummy_775)
              (syn_wrex (nb078_alpha_dummy_776) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_776)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_782 h))
          (Class.cab (nb078_alpha_dummy_777 h)
            (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_782 h))
            (Class.cab (nb078_alpha_dummy_777 h)
              (syn_wrex (nb078_alpha_dummy_778 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_776) from
                    (by
                      unfold nb078_alpha_dummy_776;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
                  (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_778 h) from (by
                      unfold nb078_alpha_dummy_778;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0804 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_775) from
                      (by
                        unfold nb078_alpha_dummy_775;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 0))))
                    (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_777 h) from (by
                        unfold nb078_alpha_dummy_777;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0804 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_781) from (by
                          unfold nb078_alpha_dummy_781;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0806) 0))))
                      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_782 h) from (by
                          unfold nb078_alpha_dummy_782;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0807 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_779) from (by
                            unfold nb078_alpha_dummy_779;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0803) 0))))
                        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_780 h) from (by
                            unfold nb078_alpha_dummy_780;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0805 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_783) from (by
                              unfold nb078_alpha_dummy_783;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                          (show (nb078_alpha_dummy_778 h) ≠ (nb078_alpha_dummy_785 h) from (by
                              unfold nb078_alpha_dummy_785;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_784) from (by
                                unfold nb078_alpha_dummy_784;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                            (show (nb078_alpha_dummy_778 h) ≠ (nb078_alpha_dummy_786 h) from (by
                                unfold nb078_alpha_dummy_786;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_778 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_790) from (by
          unfold nb078_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_793 h) from (by
          unfold nb078_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_789) from (by
          unfold nb078_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_792 h) from (by
          unfold nb078_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775),
        (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_797)
        from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_797)
        from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775),
        (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠
        (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_801)
        from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
                                        unfold nb078_alpha_dummy_787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078_alpha_dummy_785 h) ≠
                                        (nb078_alpha_dummy_788 h) from (by
                                        unfold nb078_alpha_dummy_788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
                                    ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)),
                                    ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
                                    ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
                                    ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
                                    ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
                                    ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from
                                    (by
                                      unfold nb078_alpha_dummy_787;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0810)
                                              0)))) (show
                                    (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_788 h) from
                                    (by
                                      unfold nb078_alpha_dummy_788;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0811 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
                                        unfold nb078_alpha_dummy_787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078_alpha_dummy_785 h) ≠
                                        (nb078_alpha_dummy_788 h) from (by
                                        unfold nb078_alpha_dummy_788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
                                    ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)),
                                    ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
                                    ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
                                    ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
                                    ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
                                    ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_776) from
                      (by
                        unfold nb078_alpha_dummy_776;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0802) 1))))
                    (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_778 h) from (by
                        unfold nb078_alpha_dummy_778;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0804 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_775) from (by
                          unfold nb078_alpha_dummy_775;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0802) 0))))
                      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_777 h) from (by
                          unfold nb078_alpha_dummy_777;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0804 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_781) from (by
                            unfold nb078_alpha_dummy_781;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0806) 0))))
                        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_782 h) from (by
                            unfold nb078_alpha_dummy_782;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0807 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_779) from (by
                              unfold nb078_alpha_dummy_779;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0803) 0))))
                          (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_780 h) from (by
                              unfold nb078_alpha_dummy_780;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0805 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_783) from (by
                                unfold nb078_alpha_dummy_783;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0808) 0))))
                            (show (nb078_alpha_dummy_778 h) ≠ (nb078_alpha_dummy_785 h) from (by
                                unfold nb078_alpha_dummy_785;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0809 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_784) from (by
                                  unfold nb078_alpha_dummy_784;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0808) 1))))
                              (show (nb078_alpha_dummy_778 h) ≠ (nb078_alpha_dummy_786 h) from
                                (by
                                  unfold nb078_alpha_dummy_786;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0809 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_776))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_790) from (by
          unfold nb078_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 1)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_793 h) from (by
          unfold nb078_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_789) from (by
          unfold nb078_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_792 h) from (by
          unfold nb078_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787)
        from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810)
                  0)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775),
        (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_797)
        from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_797)
        from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775),
        (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768),
        (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠
        (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_801)
        from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from
                                        (by
                                          unfold nb078_alpha_dummy_787;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0810)
                                                  0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
                                          unfold nb078_alpha_dummy_788;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0811 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
                                      ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)),
                                      ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
                                      ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
                                      ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
                                      ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
                                      ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
                                        unfold nb078_alpha_dummy_787;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0810)
                                                0)))) (show (nb078_alpha_dummy_785 h) ≠
                                        (nb078_alpha_dummy_788 h) from (by
                                        unfold nb078_alpha_dummy_788;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0811 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from
                                        (by
                                          unfold nb078_alpha_dummy_787;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0810)
                                                  0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
                                          unfold nb078_alpha_dummy_788;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0811 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
                                      ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)),
                                      ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
                                      ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
                                      ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
                                      ((nb078_alpha_dummy_781), (nb078_alpha_dummy_782 h)),
                                      ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part136`. -/


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
noncomputable def nb078_split_alpha_0114 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
        ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
        ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)),
        ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_776))
          (Class.cv (nb078_alpha_dummy_768))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_775))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_776))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_778 h))
          (Class.cv (nb078_alpha_dummy_771 h))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_777 h))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_778 h))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_776) from (by
              unfold nb078_alpha_dummy_776;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 1))))
          (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_778 h) from (by
              unfold nb078_alpha_dummy_778;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_775) from (by
                unfold nb078_alpha_dummy_775;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0830) 0))))
            (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_777 h) from (by
                unfold nb078_alpha_dummy_777;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0832 h) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_805) from (by
                  unfold nb078_alpha_dummy_805;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0834) 0))))
              (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_806 h) from (by
                  unfold nb078_alpha_dummy_806;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0835 h) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_779) from (by
                    unfold nb078_alpha_dummy_779;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0831) 0))))
                (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_780 h) from (by
                    unfold nb078_alpha_dummy_780;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0833 h) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                ((Class.cv (nb078_alpha_dummy_768))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                ((Class.cv (nb078_alpha_dummy_771 h))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_783) from (by
                                        unfold nb078_alpha_dummy_783;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0808)
                                                0)))) (show (nb078_alpha_dummy_778 h) ≠
                                        (nb078_alpha_dummy_785 h) from (by
                                        unfold nb078_alpha_dummy_785;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0809 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_784) from
                                        (by
                                          unfold nb078_alpha_dummy_784;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0808)
                                                  1)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_786 h) from (by
                                          unfold nb078_alpha_dummy_786;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0809 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_776) ≠
        (nb078_alpha_dummy_809) from (by
          unfold nb078_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0838) 0)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_810 h) from (by
          unfold nb078_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0839 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_807) from (by
          unfold nb078_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0836) 0)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_808 h) from (by
          unfold nb078_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0837 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_790) from (by
          unfold nb078_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812)
                  1)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_793 h) from (by
          unfold nb078_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_789)
        from (by
          unfold nb078_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812)
                  0)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_792 h) from (by
          unfold nb078_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787)
        from (by
          unfold
            nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810)
                  0)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_788 h) from (by
          unfold
            nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807),
        (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
        ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805),
        (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807),
        (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
        ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805),
        (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠
        (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787)
        from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
        ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784),
        (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)),
        ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776),
        (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
        ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779),
        (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
        ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784),
        (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)),
        ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776),
        (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
        ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779),
        (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_783) from (by
                                        unfold nb078_alpha_dummy_783;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0808)
                                                0)))) (show (nb078_alpha_dummy_778 h) ≠
                                        (nb078_alpha_dummy_785 h) from (by
                                        unfold nb078_alpha_dummy_785;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0809 h)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_784) from
                                        (by
                                          unfold nb078_alpha_dummy_784;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0808)
                                                  1)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_786 h) from (by
                                          unfold nb078_alpha_dummy_786;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0809 h) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_776) ≠
        (nb078_alpha_dummy_809) from (by
          unfold nb078_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0838) 0)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_810 h) from (by
          unfold nb078_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0839 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_776) ≠ (nb078_alpha_dummy_807) from (by
          unfold nb078_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0836) 0)))) (show (nb078_alpha_dummy_778 h) ≠
        (nb078_alpha_dummy_808 h) from (by
          unfold nb078_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0837 h) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_776))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_778 h))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_790) from (by
          unfold nb078_alpha_dummy_790;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812)
                  1)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_793 h) from (by
          unfold nb078_alpha_dummy_793;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813
                    h)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_789)
        from (by
          unfold nb078_alpha_dummy_789;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0812)
                  0)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_792 h) from (by
          unfold nb078_alpha_dummy_792;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0813
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787)
        from (by
          unfold
            nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810)
                  0)))) (show (nb078_alpha_dummy_785 h) ≠ (nb078_alpha_dummy_788 h) from (by
          unfold
            nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807),
        (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
        ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805),
        (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0816)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0817
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0814)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0815
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_797) from (by
          unfold
            nb078_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0820)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_798 h) from (by
          unfold
            nb078_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0821
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_795)
        from (by
          unfold
            nb078_alpha_dummy_795;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0818)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_796 h) from (by
          unfold
            nb078_alpha_dummy_796;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0819
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_791), (nb078_alpha_dummy_794 h)), ((nb078_alpha_dummy_790),
        (nb078_alpha_dummy_793 h)), ((nb078_alpha_dummy_789), (nb078_alpha_dummy_792 h)),
        ((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)), ((nb078_alpha_dummy_783),
        (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784), (nb078_alpha_dummy_786 h)),
        ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)), ((nb078_alpha_dummy_807),
        (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
        ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)), ((nb078_alpha_dummy_805),
        (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)), ((nb078_alpha_dummy_767),
        (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_783))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠
        (nb078_alpha_dummy_801) from (by
          unfold
            nb078_alpha_dummy_801;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0824)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_802 h) from (by
          unfold
            nb078_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0825
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_790) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0822)
                  0)))) (show (nb078_alpha_dummy_793 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0823
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_783))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_785 h))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠
        (nb078_alpha_dummy_803) from (by
          unfold
            nb078_alpha_dummy_803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0828)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_804 h) from (by
          unfold
            nb078_alpha_dummy_804;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0829
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_791) ≠ (nb078_alpha_dummy_799)
        from (by
          unfold
            nb078_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0826)
                  0)))) (show (nb078_alpha_dummy_794 h) ≠ (nb078_alpha_dummy_800 h) from (by
          unfold
            nb078_alpha_dummy_800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0827
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787)
        from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
        ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784),
        (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)),
        ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776),
        (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
        ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779),
        (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_783) ≠ (nb078_alpha_dummy_787) from (by
          unfold nb078_alpha_dummy_787;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0810) 0)))) (show (nb078_alpha_dummy_785 h) ≠
        (nb078_alpha_dummy_788 h) from (by
          unfold nb078_alpha_dummy_788;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0811 h) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_787), (nb078_alpha_dummy_788 h)),
        ((nb078_alpha_dummy_783), (nb078_alpha_dummy_785 h)), ((nb078_alpha_dummy_784),
        (nb078_alpha_dummy_786 h)), ((nb078_alpha_dummy_809), (nb078_alpha_dummy_810 h)),
        ((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)), ((nb078_alpha_dummy_776),
        (nb078_alpha_dummy_778 h)), ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
        ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)), ((nb078_alpha_dummy_779),
        (nb078_alpha_dummy_780 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_807), (nb078_alpha_dummy_808 h)),
                    ((nb078_alpha_dummy_776), (nb078_alpha_dummy_778 h)),
                    ((nb078_alpha_dummy_775), (nb078_alpha_dummy_777 h)),
                    ((nb078_alpha_dummy_805), (nb078_alpha_dummy_806 h)),
                    ((nb078_alpha_dummy_779), (nb078_alpha_dummy_780 h)),
                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part137`. -/


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
noncomputable def nb078_split_alpha_0115 (x : Var) (y : Var) (h : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
        ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
        ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
        ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
        ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_817))
          (Class.cab (nb078_alpha_dummy_811)
            (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                (syn_cphi (Class.cv (nb078_alpha_dummy_812))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_817)) (Class.cab (nb078_alpha_dummy_811)
              (syn_wrex (nb078_alpha_dummy_812) (Class.cv (nb078_alpha_dummy_767))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_811))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_812)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_818 h))
          (Class.cab (nb078_alpha_dummy_813 h)
            (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_818 h))
            (Class.cab (nb078_alpha_dummy_813 h)
              (syn_wrex (nb078_alpha_dummy_814 h) (Class.cv (nb078_alpha_dummy_770 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_813 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_814 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_812) from
                    (by
                      unfold nb078_alpha_dummy_812;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
                  (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_814 h) from (by
                      unfold nb078_alpha_dummy_814;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0842 h) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_811) from
                      (by
                        unfold nb078_alpha_dummy_811;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 0))))
                    (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_813 h) from (by
                        unfold nb078_alpha_dummy_813;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0842 h) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_817) from (by
                          unfold nb078_alpha_dummy_817;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0844) 0))))
                      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_818 h) from (by
                          unfold nb078_alpha_dummy_818;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0845 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_815) from (by
                            unfold nb078_alpha_dummy_815;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0841) 0))))
                        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_816 h) from (by
                            unfold nb078_alpha_dummy_816;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0843 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                              ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                          (freshVar_injective (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv)
                            (by decide)) (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_769))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_819) from (by
                              unfold nb078_alpha_dummy_819;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                          (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_821 h) from (by
                              unfold nb078_alpha_dummy_821;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_820) from (by
                                unfold nb078_alpha_dummy_820;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                            (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_822 h) from (by
                                unfold nb078_alpha_dummy_822;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_814 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_826) from (by
          unfold nb078_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_829 h) from (by
          unfold nb078_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_825) from (by
          unfold nb078_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_828 h) from (by
          unfold nb078_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
          unfold nb078_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848) 0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
          unfold nb078_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811),
        (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811),
        (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837) from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837)
        from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠
        (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
                                        unfold nb078_alpha_dummy_823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078_alpha_dummy_821 h) ≠
                                        (nb078_alpha_dummy_824 h) from (by
                                        unfold nb078_alpha_dummy_824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                    ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                    ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                    ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                    ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                    ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
                                    ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                    (by
                                      unfold nb078_alpha_dummy_823;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0848)
                                              0)))) (show
                                    (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_824 h) from
                                    (by
                                      unfold nb078_alpha_dummy_824;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0849 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
                                        unfold nb078_alpha_dummy_823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078_alpha_dummy_821 h) ≠
                                        (nb078_alpha_dummy_824 h) from (by
                                        unfold nb078_alpha_dummy_824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                    ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                    ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                    ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                    ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                    ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
                                    ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                    ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                    ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                    ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                    ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                    ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_812) from
                      (by
                        unfold nb078_alpha_dummy_812;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0840) 1))))
                    (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_814 h) from (by
                        unfold nb078_alpha_dummy_814;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0842 h) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_811) from (by
                          unfold nb078_alpha_dummy_811;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0840) 0))))
                      (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_813 h) from (by
                          unfold nb078_alpha_dummy_813;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0842 h) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_817) from (by
                            unfold nb078_alpha_dummy_817;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0844) 0))))
                        (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_818 h) from (by
                            unfold nb078_alpha_dummy_818;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0845 h) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_767) ≠ (nb078_alpha_dummy_815) from (by
                              unfold nb078_alpha_dummy_815;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0841) 0))))
                          (show (nb078_alpha_dummy_770 h) ≠ (nb078_alpha_dummy_816 h) from (by
                              unfold nb078_alpha_dummy_816;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0843 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                                ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb078_alpha_dummy_002))).fv ∪
                                  ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_767))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_769))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_770 h))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_772 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_819) from (by
                                unfold nb078_alpha_dummy_819;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0846) 0))))
                            (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_821 h) from (by
                                unfold nb078_alpha_dummy_821;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0847 h) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_812) ≠ (nb078_alpha_dummy_820) from (by
                                  unfold nb078_alpha_dummy_820;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0846) 1))))
                              (show (nb078_alpha_dummy_814 h) ≠ (nb078_alpha_dummy_822 h) from
                                (by
                                  unfold nb078_alpha_dummy_822;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0847 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_812))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_814 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_826) from (by
          unfold nb078_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 1)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_829 h) from (by
          unfold nb078_alpha_dummy_829;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_825) from (by
          unfold nb078_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0850) 0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_828 h) from (by
          unfold nb078_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0851 h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823)
        from (by
          unfold nb078_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0848)
                  0)))) (show (nb078_alpha_dummy_821 h) ≠ (nb078_alpha_dummy_824 h) from (by
          unfold nb078_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0849 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811),
        (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_833) from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0854)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0855
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0852)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0853
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_833)
        from (by
          unfold
            nb078_alpha_dummy_833;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0858)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_834 h) from (by
          unfold
            nb078_alpha_dummy_834;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0859
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_831)
        from (by
          unfold
            nb078_alpha_dummy_831;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0856)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_832 h) from (by
          unfold
            nb078_alpha_dummy_832;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0857
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_827), (nb078_alpha_dummy_830 h)), ((nb078_alpha_dummy_826),
        (nb078_alpha_dummy_829 h)), ((nb078_alpha_dummy_825), (nb078_alpha_dummy_828 h)),
        ((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)), ((nb078_alpha_dummy_819),
        (nb078_alpha_dummy_821 h)), ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
        ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)), ((nb078_alpha_dummy_811),
        (nb078_alpha_dummy_813 h)), ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
        ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)), ((nb078_alpha_dummy_769),
        (nb078_alpha_dummy_772 h)), ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
        ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)), ((nb078_alpha_dummy_773),
        (nb078_alpha_dummy_774 h)), ((nb078_alpha_dummy_002), h), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_819))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_821
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837) from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_837)
        from (by
          unfold
            nb078_alpha_dummy_837;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0862)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_838 h) from (by
          unfold
            nb078_alpha_dummy_838;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0863
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_826) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0860)
                  0)))) (show (nb078_alpha_dummy_829 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0861
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_819))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_821 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠
        (nb078_alpha_dummy_839) from (by
          unfold
            nb078_alpha_dummy_839;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0866)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_840 h) from (by
          unfold
            nb078_alpha_dummy_840;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0867
                    h)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_827) ≠ (nb078_alpha_dummy_835)
        from (by
          unfold
            nb078_alpha_dummy_835;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0864)
                  0)))) (show (nb078_alpha_dummy_830 h) ≠ (nb078_alpha_dummy_836 h) from (by
          unfold
            nb078_alpha_dummy_836;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0865
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from (by
                                        unfold nb078_alpha_dummy_823;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0848)
                                                0)))) (show (nb078_alpha_dummy_821 h) ≠
                                        (nb078_alpha_dummy_824 h) from (by
                                        unfold nb078_alpha_dummy_824;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0849 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_819) ≠ (nb078_alpha_dummy_823) from
                                        (by
                                          unfold nb078_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0848)
                                                  0)))) (show (nb078_alpha_dummy_821 h) ≠
        (nb078_alpha_dummy_824 h) from (by
                                          unfold nb078_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0849 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_823), (nb078_alpha_dummy_824 h)),
                                      ((nb078_alpha_dummy_819), (nb078_alpha_dummy_821 h)),
                                      ((nb078_alpha_dummy_820), (nb078_alpha_dummy_822 h)),
                                      ((nb078_alpha_dummy_812), (nb078_alpha_dummy_814 h)),
                                      ((nb078_alpha_dummy_811), (nb078_alpha_dummy_813 h)),
                                      ((nb078_alpha_dummy_817), (nb078_alpha_dummy_818 h)),
                                      ((nb078_alpha_dummy_815), (nb078_alpha_dummy_816 h)),
                                      ((nb078_alpha_dummy_769), (nb078_alpha_dummy_772 h)),
                                      ((nb078_alpha_dummy_768), (nb078_alpha_dummy_771 h)),
                                      ((nb078_alpha_dummy_767), (nb078_alpha_dummy_770 h)),
                                      ((nb078_alpha_dummy_773), (nb078_alpha_dummy_774 h)),
                                      ((nb078_alpha_dummy_002), h),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
