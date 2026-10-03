/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block041

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part115`. -/


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
noncomputable def nb090_split_alpha_0092 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_819 A), (nb090_alpha_dummy_820 v u h)),
        ((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)),
        ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)),
        ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)),
        ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)),
        ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)),
        ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)),
        ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
        ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)),
        ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)),
        ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
        ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
        ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
        ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_819 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_819 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_820 v u h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_820 v u h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_793 A) from (by
                      unfold nb090_alpha_dummy_793;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0834 A) 0))))
                  (show (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_795 v u h) from (by
                      unfold nb090_alpha_dummy_795;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0835 v u h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_794 A) from (by
                        unfold nb090_alpha_dummy_794;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0834 A) 1))))
                    (show (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_796 v u h) from (by
                        unfold nb090_alpha_dummy_796;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0835 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_819 A) from (by
                          unfold nb090_alpha_dummy_819;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0864 A) 0))))
                      (show (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_820 v u h) from
                        (by
                          unfold nb090_alpha_dummy_820;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0865 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_817 A) from (by
                            unfold nb090_alpha_dummy_817;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0862 A) 0)))) (show
                          (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_818 v u h) from (by
                            unfold nb090_alpha_dummy_818;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0863 v u h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_786 A))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_788 v u h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_800 A) from
                                      (by
                                        unfold nb090_alpha_dummy_800;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0838 A)
                                                1)))) (show (nb090_alpha_dummy_795 v u h) ≠
                                        (nb090_alpha_dummy_803 v u h) from (by
                                        unfold nb090_alpha_dummy_803;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0839 v u h) 1))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_793 A) ≠
        (nb090_alpha_dummy_799 A) from (by
                                          unfold nb090_alpha_dummy_799;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0838 A) 0)))) (show
                                        (nb090_alpha_dummy_795 v u h) ≠
        (nb090_alpha_dummy_802 v u h) from (by
                                          unfold nb090_alpha_dummy_802;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0839 v u h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_793 A) ≠
        (nb090_alpha_dummy_797 A) from (by
          unfold nb090_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A) 0)))) (show (nb090_alpha_dummy_795 v u h) ≠
        (nb090_alpha_dummy_798 v u h) from (by
          unfold nb090_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_801 A),
        (nb090_alpha_dummy_804 v u h)), ((nb090_alpha_dummy_800 A),
        (nb090_alpha_dummy_803 v u h)), ((nb090_alpha_dummy_799 A),
        (nb090_alpha_dummy_802 v u h)), ((nb090_alpha_dummy_797 A),
        (nb090_alpha_dummy_798 v u h)), ((nb090_alpha_dummy_793 A),
        (nb090_alpha_dummy_795 v u h)), ((nb090_alpha_dummy_794 A),
        (nb090_alpha_dummy_796 v u h)), ((nb090_alpha_dummy_819 A),
        (nb090_alpha_dummy_820 v u h)), ((nb090_alpha_dummy_817 A),
        (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A),
        (nb090_alpha_dummy_787 v u h)), ((nb090_alpha_dummy_815 A),
        (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789 A),
        (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A),
        (nb090_alpha_dummy_778 v u h)), ((nb090_alpha_dummy_779 A),
        (nb090_alpha_dummy_780 v u h)), ((nb090_alpha_dummy_782 A),
        (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_801 A),
        (nb090_alpha_dummy_804 v u h)), ((nb090_alpha_dummy_800 A),
        (nb090_alpha_dummy_803 v u h)), ((nb090_alpha_dummy_799 A),
        (nb090_alpha_dummy_802 v u h)), ((nb090_alpha_dummy_797 A),
        (nb090_alpha_dummy_798 v u h)), ((nb090_alpha_dummy_793 A),
        (nb090_alpha_dummy_795 v u h)), ((nb090_alpha_dummy_794 A),
        (nb090_alpha_dummy_796 v u h)), ((nb090_alpha_dummy_819 A),
        (nb090_alpha_dummy_820 v u h)), ((nb090_alpha_dummy_817 A),
        (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A),
        (nb090_alpha_dummy_787 v u h)), ((nb090_alpha_dummy_815 A),
        (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789 A),
        (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A),
        (nb090_alpha_dummy_778 v u h)), ((nb090_alpha_dummy_779 A),
        (nb090_alpha_dummy_780 v u h)), ((nb090_alpha_dummy_782 A),
        (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_811 A) from (by
          unfold
            nb090_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_812 v u h) from
        (by
          unfold
            nb090_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_811 A) from (by
          unfold
            nb090_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_812 v u h) from
        (by
          unfold
            nb090_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_813 A) from (by
          unfold
            nb090_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_814 v u h) from
        (by
          unfold
            nb090_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_813 A) from (by
          unfold
            nb090_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_814 v u h) from
        (by
          unfold
            nb090_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from (by
                                unfold nb090_alpha_dummy_797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h) from
                              (by
                                unfold nb090_alpha_dummy_798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_797 A), (nb090_alpha_dummy_798 v u h)),
                            ((nb090_alpha_dummy_793 A), (nb090_alpha_dummy_795 v u h)),
                            ((nb090_alpha_dummy_794 A), (nb090_alpha_dummy_796 v u h)),
                            ((nb090_alpha_dummy_819 A), (nb090_alpha_dummy_820 v u h)),
                            ((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)),
                            ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)),
                            ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)),
                            ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)),
                            ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)),
                            ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)),
                            ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
                            ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)),
                            ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)),
                            ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                            ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                            ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
                            ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from (by
                              unfold nb090_alpha_dummy_797;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                            (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h) from
                            (by
                              unfold nb090_alpha_dummy_798;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0837 v u h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from (by
                                unfold nb090_alpha_dummy_797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h) from
                              (by
                                unfold nb090_alpha_dummy_798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_797 A), (nb090_alpha_dummy_798 v u h)),
                            ((nb090_alpha_dummy_793 A), (nb090_alpha_dummy_795 v u h)),
                            ((nb090_alpha_dummy_794 A), (nb090_alpha_dummy_796 v u h)),
                            ((nb090_alpha_dummy_819 A), (nb090_alpha_dummy_820 v u h)),
                            ((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)),
                            ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)),
                            ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)),
                            ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)),
                            ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)),
                            ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)),
                            ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
                            ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)),
                            ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)),
                            ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                            ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                            ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
                            ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_793 A) from (by
                        unfold nb090_alpha_dummy_793;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0834 A) 0))))
                    (show (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_795 v u h) from (by
                        unfold nb090_alpha_dummy_795;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0835 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_794 A) from (by
                          unfold nb090_alpha_dummy_794;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0834 A) 1))))
                      (show (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_796 v u h) from
                        (by
                          unfold nb090_alpha_dummy_796;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0835 v u h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_819 A) from (by
                            unfold nb090_alpha_dummy_819;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0864 A) 0)))) (show
                          (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_820 v u h) from (by
                            unfold nb090_alpha_dummy_820;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0865 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_786 A) ≠ (nb090_alpha_dummy_817 A) from (by
                              unfold nb090_alpha_dummy_817;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0862 A) 0)))) (show
                            (nb090_alpha_dummy_788 v u h) ≠ (nb090_alpha_dummy_818 v u h) from
                            (by
                              unfold nb090_alpha_dummy_818;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0863 v u h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_786 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_788 v u h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_793 A) ≠
        (nb090_alpha_dummy_800 A) from (by
                                          unfold nb090_alpha_dummy_800;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0838 A) 1)))) (show
                                        (nb090_alpha_dummy_795 v u h) ≠
        (nb090_alpha_dummy_803 v u h) from (by
                                          unfold nb090_alpha_dummy_803;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0839 v u h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_793 A) ≠
        (nb090_alpha_dummy_799 A) from (by
          unfold nb090_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A) 0)))) (show (nb090_alpha_dummy_795 v u h) ≠
        (nb090_alpha_dummy_802 v u h) from (by
          unfold nb090_alpha_dummy_802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from (by
          unfold nb090_alpha_dummy_797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A) 0)))) (show (nb090_alpha_dummy_795 v u h) ≠
        (nb090_alpha_dummy_798 v u h) from (by
          unfold nb090_alpha_dummy_798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_801 A),
        (nb090_alpha_dummy_804 v u h)), ((nb090_alpha_dummy_800 A),
        (nb090_alpha_dummy_803 v u h)), ((nb090_alpha_dummy_799 A),
        (nb090_alpha_dummy_802 v u h)), ((nb090_alpha_dummy_797 A),
        (nb090_alpha_dummy_798 v u h)), ((nb090_alpha_dummy_793 A),
        (nb090_alpha_dummy_795 v u h)), ((nb090_alpha_dummy_794 A),
        (nb090_alpha_dummy_796 v u h)), ((nb090_alpha_dummy_819 A),
        (nb090_alpha_dummy_820 v u h)), ((nb090_alpha_dummy_817 A),
        (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A),
        (nb090_alpha_dummy_787 v u h)), ((nb090_alpha_dummy_815 A),
        (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789 A),
        (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A),
        (nb090_alpha_dummy_778 v u h)), ((nb090_alpha_dummy_779 A),
        (nb090_alpha_dummy_780 v u h)), ((nb090_alpha_dummy_782 A),
        (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_807 A) from (by
          unfold
            nb090_alpha_dummy_807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_808 v u h) from
        (by
          unfold
            nb090_alpha_dummy_808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_805 A) from (by
          unfold
            nb090_alpha_dummy_805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_806 v u h) from
        (by
          unfold
            nb090_alpha_dummy_806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_801 A), (nb090_alpha_dummy_804 v u h)), ((nb090_alpha_dummy_800 A),
        (nb090_alpha_dummy_803 v u h)), ((nb090_alpha_dummy_799 A),
        (nb090_alpha_dummy_802 v u h)), ((nb090_alpha_dummy_797 A),
        (nb090_alpha_dummy_798 v u h)), ((nb090_alpha_dummy_793 A),
        (nb090_alpha_dummy_795 v u h)), ((nb090_alpha_dummy_794 A),
        (nb090_alpha_dummy_796 v u h)), ((nb090_alpha_dummy_819 A),
        (nb090_alpha_dummy_820 v u h)), ((nb090_alpha_dummy_817 A),
        (nb090_alpha_dummy_818 v u h)), ((nb090_alpha_dummy_786 A),
        (nb090_alpha_dummy_788 v u h)), ((nb090_alpha_dummy_785 A),
        (nb090_alpha_dummy_787 v u h)), ((nb090_alpha_dummy_815 A),
        (nb090_alpha_dummy_816 v u h)), ((nb090_alpha_dummy_789 A),
        (nb090_alpha_dummy_790 v u h)), ((nb090_alpha_dummy_777 A),
        (nb090_alpha_dummy_778 v u h)), ((nb090_alpha_dummy_779 A),
        (nb090_alpha_dummy_780 v u h)), ((nb090_alpha_dummy_782 A),
        (nb090_alpha_dummy_784 v u h)), ((nb090_alpha_dummy_781 A),
        (nb090_alpha_dummy_783 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_811 A) from (by
          unfold
            nb090_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_812 v u h) from
        (by
          unfold
            nb090_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠ (nb090_alpha_dummy_811 A) from (by
          unfold
            nb090_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_812 v u h) from
        (by
          unfold
            nb090_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_800 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090_alpha_dummy_803 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_793
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_813 A) from (by
          unfold
            nb090_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_814 v u h) from
        (by
          unfold
            nb090_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_801 A) ≠ (nb090_alpha_dummy_813 A) from (by
          unfold
            nb090_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_814 v u h) from
        (by
          unfold
            nb090_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_801 A) ≠
        (nb090_alpha_dummy_809 A) from (by
          unfold
            nb090_alpha_dummy_809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090_alpha_dummy_804 v u h) ≠ (nb090_alpha_dummy_810 v u h) from
        (by
          unfold
            nb090_alpha_dummy_810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from
                                (by
                                  unfold nb090_alpha_dummy_797;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                                (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_798;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_797 A), (nb090_alpha_dummy_798 v u h)),
                              ((nb090_alpha_dummy_793 A), (nb090_alpha_dummy_795 v u h)),
                              ((nb090_alpha_dummy_794 A), (nb090_alpha_dummy_796 v u h)),
                              ((nb090_alpha_dummy_819 A), (nb090_alpha_dummy_820 v u h)),
                              ((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)),
                              ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)),
                              ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)),
                              ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)),
                              ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)),
                              ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)),
                              ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
                              ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)),
                              ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)),
                              ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                              ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                              ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
                              ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from (by
                                unfold nb090_alpha_dummy_797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h) from
                              (by
                                unfold nb090_alpha_dummy_798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_793 A) ≠ (nb090_alpha_dummy_797 A) from
                                (by
                                  unfold nb090_alpha_dummy_797;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                                (nb090_alpha_dummy_795 v u h) ≠ (nb090_alpha_dummy_798 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_798;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_797 A), (nb090_alpha_dummy_798 v u h)),
                              ((nb090_alpha_dummy_793 A), (nb090_alpha_dummy_795 v u h)),
                              ((nb090_alpha_dummy_794 A), (nb090_alpha_dummy_796 v u h)),
                              ((nb090_alpha_dummy_819 A), (nb090_alpha_dummy_820 v u h)),
                              ((nb090_alpha_dummy_817 A), (nb090_alpha_dummy_818 v u h)),
                              ((nb090_alpha_dummy_786 A), (nb090_alpha_dummy_788 v u h)),
                              ((nb090_alpha_dummy_785 A), (nb090_alpha_dummy_787 v u h)),
                              ((nb090_alpha_dummy_815 A), (nb090_alpha_dummy_816 v u h)),
                              ((nb090_alpha_dummy_789 A), (nb090_alpha_dummy_790 v u h)),
                              ((nb090_alpha_dummy_777 A), (nb090_alpha_dummy_778 v u h)),
                              ((nb090_alpha_dummy_779 A), (nb090_alpha_dummy_780 v u h)),
                              ((nb090_alpha_dummy_782 A), (nb090_alpha_dummy_784 v u h)),
                              ((nb090_alpha_dummy_781 A), (nb090_alpha_dummy_783 v u h)),
                              ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                              ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                              ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
                              ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part116`. -/


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
noncomputable def nb090_split_alpha_0093 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
        ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
        ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
        ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
        (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))) (syn_csn (syn_c0c))))
      (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
        (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))) (syn_csn (syn_c0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
            ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))).fv) (by decide)) (freshVar_injective
          (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
            ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_700 A) ≠ (nb090_alpha_dummy_753 A) from (by
                                    unfold nb090_alpha_dummy_753;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0794 A)
                                            0)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                    (nb090_alpha_dummy_755 v u h) from (by
                                    unfold nb090_alpha_dummy_755;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_700 A) ≠ (nb090_alpha_dummy_754 A) from
                                    (by
                                      unfold nb090_alpha_dummy_754;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0794 A)
                                              1)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                      (nb090_alpha_dummy_756 v u h) from (by
                                      unfold nb090_alpha_dummy_756;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0795 v u h) 1))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_700 A) ≠
                                        (nb090_alpha_dummy_825 A) from (by
                                        unfold nb090_alpha_dummy_825;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0878 A)
                                                0)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                        (nb090_alpha_dummy_826 v u h) from (by
                                        unfold nb090_alpha_dummy_826;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0879 v u h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_700 A) ≠
        (nb090_alpha_dummy_823 A) from (by
                                          unfold nb090_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0876 A) 0)))) (show
                                        (nb090_alpha_dummy_702 v u h) ≠
        (nb090_alpha_dummy_824 v u h) from (by
                                          unfold nb090_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0877 v u h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_700 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_760 A) from (by
          unfold nb090_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  1)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_763 v u h) from
        (by
          unfold nb090_alpha_dummy_763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_759 A) from (by
          unfold nb090_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  0)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_762 v u h) from
        (by
          unfold nb090_alpha_dummy_762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796
                    A)
                  0)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_758 v u h) from
        (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A),
        (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A),
        (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A),
        (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A),
        (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_771 A) from (by
          unfold
            nb090_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_772 v u h) from
        (by
          unfold
            nb090_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_771 A) from (by
          unfold
            nb090_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_772 v u h) from
        (by
          unfold
            nb090_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_773 A) from (by
          unfold
            nb090_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_774 v u h) from
        (by
          unfold
            nb090_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_761
        A) ≠ (nb090_alpha_dummy_773 A) from (by
          unfold
            nb090_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_774 v u h) from
        (by
          unfold
            nb090_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_700 A) ≠ (nb090_alpha_dummy_753 A) from (by
                                    unfold nb090_alpha_dummy_753;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0794 A)
                                            0)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                    (nb090_alpha_dummy_755 v u h) from (by
                                    unfold nb090_alpha_dummy_755;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_700 A) ≠ (nb090_alpha_dummy_754 A) from
                                    (by
                                      unfold nb090_alpha_dummy_754;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0794 A)
                                              1)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                      (nb090_alpha_dummy_756 v u h) from (by
                                      unfold nb090_alpha_dummy_756;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0795 v u h) 1))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_700 A) ≠
                                        (nb090_alpha_dummy_825 A) from (by
                                        unfold nb090_alpha_dummy_825;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0878 A)
                                                0)))) (show (nb090_alpha_dummy_702 v u h) ≠
                                        (nb090_alpha_dummy_826 v u h) from (by
                                        unfold nb090_alpha_dummy_826;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0879 v u h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_700 A) ≠
        (nb090_alpha_dummy_823 A) from (by
                                          unfold nb090_alpha_dummy_823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0876 A) 0)))) (show
                                        (nb090_alpha_dummy_702 v u h) ≠
        (nb090_alpha_dummy_824 v u h) from (by
                                          unfold nb090_alpha_dummy_824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0877 v u h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_700 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_760 A) from (by
          unfold nb090_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  1)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_763 v u h) from
        (by
          unfold nb090_alpha_dummy_763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u
                    h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_759 A) from (by
          unfold nb090_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  0)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_762 v u h) from
        (by
          unfold nb090_alpha_dummy_762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796
                    A)
                  0)))) (show (nb090_alpha_dummy_755 v u h) ≠ (nb090_alpha_dummy_758 v u h) from
        (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A),
        (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A),
        (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠ (nb090_alpha_dummy_767 A) from (by
          unfold
            nb090_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_768 v u h) from
        (by
          unfold
            nb090_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_765 A) from (by
          unfold
            nb090_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_766 v u h) from
        (by
          unfold
            nb090_alpha_dummy_766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_761 A), (nb090_alpha_dummy_764 v u h)), ((nb090_alpha_dummy_760 A),
        (nb090_alpha_dummy_763 v u h)), ((nb090_alpha_dummy_759 A),
        (nb090_alpha_dummy_762 v u h)), ((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_c0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_771 A) from (by
          unfold
            nb090_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_772 v u h) from
        (by
          unfold
            nb090_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠ (nb090_alpha_dummy_771 A) from (by
          unfold
            nb090_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_772 v u h) from
        (by
          unfold
            nb090_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_760 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090_alpha_dummy_763 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_753
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_773 A) from (by
          unfold
            nb090_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_774 v u h) from
        (by
          unfold
            nb090_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_761
        A) ≠ (nb090_alpha_dummy_773 A) from (by
          unfold
            nb090_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_774 v u h) from
        (by
          unfold
            nb090_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_761 A) ≠
        (nb090_alpha_dummy_769 A) from (by
          unfold
            nb090_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090_alpha_dummy_764 v u h) ≠ (nb090_alpha_dummy_770 v u h) from
        (by
          unfold
            nb090_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090_alpha_dummy_753 A) ≠
        (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_753 A) ≠ (nb090_alpha_dummy_757 A) from (by
          unfold nb090_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090_alpha_dummy_755 v u h) ≠
        (nb090_alpha_dummy_758 v u h) from (by
          unfold nb090_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_757 A),
        (nb090_alpha_dummy_758 v u h)), ((nb090_alpha_dummy_753 A),
        (nb090_alpha_dummy_755 v u h)), ((nb090_alpha_dummy_754 A),
        (nb090_alpha_dummy_756 v u h)), ((nb090_alpha_dummy_825 A),
        (nb090_alpha_dummy_826 v u h)), ((nb090_alpha_dummy_823 A),
        (nb090_alpha_dummy_824 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_775 A),
        (nb090_alpha_dummy_776 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.refl_of_closed
              [((nb090_alpha_dummy_823 A), (nb090_alpha_dummy_824 v u h)),
                ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                ((nb090_alpha_dummy_775 A), (nb090_alpha_dummy_776 v u h)),
                ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                ((nb090_alpha_dummy_001 A), u),
                ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
              (syn_ccompl (syn_csn (syn_c0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))

theorem nb090_compact_fv_empty_0640 (A : Class) :
    (nb090_alpha_dummy_827 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0641 (v : Var) :
    (nb090_alpha_dummy_828 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0642 (A : Class) :
    (nb090_alpha_dummy_829 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0643 (v : Var) :
    (nb090_alpha_dummy_830 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0644 (A : Class) :
    (nb090_alpha_dummy_832 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0645 (v : Var) :
    (nb090_alpha_dummy_834 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0646 (A : Class) :
    (nb090_alpha_dummy_831 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0647 (v : Var) :
    (nb090_alpha_dummy_833 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
