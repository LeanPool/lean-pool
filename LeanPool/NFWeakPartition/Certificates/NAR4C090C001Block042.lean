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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0092`. -/
@[expose]
noncomputable def nb090SplitAlpha0092 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy819 A), (nb090AlphaDummy820 v u h)),
        ((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)),
        ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
        ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
        ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)),
        ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
        ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
        ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
        ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
        ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
        ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
        ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy819 A))
          (synCphi (Class.cv (nb090AlphaDummy786 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy819 A))
            (synCphi (Class.cv (nb090AlphaDummy786 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy820 v u h))
          (synCphi (Class.cv (nb090AlphaDummy788 v u h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy820 v u h))
            (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy793 A) from (by
                      unfold nb090AlphaDummy793;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0834 A) 0))))
                  (show (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy795 v u h) from (by
                      unfold nb090AlphaDummy795;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0835 v u h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy794 A) from (by
                        unfold nb090AlphaDummy794;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0834 A) 1))))
                    (show (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy796 v u h) from (by
                        unfold nb090AlphaDummy796;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0835 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy819 A) from (by
                          unfold nb090AlphaDummy819;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0864 A) 0))))
                      (show (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy820 v u h) from
                        (by
                          unfold nb090AlphaDummy820;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0865 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy817 A) from (by
                            unfold nb090AlphaDummy817;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0862 A) 0)))) (show
                          (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy818 v u h) from (by
                            unfold nb090AlphaDummy818;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0863 v u h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy786 A))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy788 v u h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy800 A) from
                                      (by
                                        unfold nb090AlphaDummy800;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0838 A)
                                                1)))) (show (nb090AlphaDummy795 v u h) ≠
                                        (nb090AlphaDummy803 v u h) from (by
                                        unfold nb090AlphaDummy803;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0839 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy799 A) from (by
                                          unfold nb090AlphaDummy799;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0838 A) 0)))) (show
                                        (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy802 v u h) from (by
                                          unfold nb090AlphaDummy802;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0839 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy797 A) from (by
          unfold nb090AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A) 0)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy798 v u h) from (by
          unfold nb090AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy801 A),
        (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy819 A),
        (nb090AlphaDummy820 v u h)), ((nb090AlphaDummy817 A),
        (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy815 A),
        (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy801 A),
        (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy819 A),
        (nb090AlphaDummy820 v u h)), ((nb090AlphaDummy817 A),
        (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy815 A),
        (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from (by
                                unfold nb090AlphaDummy797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
                              (by
                                unfold nb090AlphaDummy798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                            ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                            ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                            ((nb090AlphaDummy819 A), (nb090AlphaDummy820 v u h)),
                            ((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)),
                            ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                            ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                            ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)),
                            ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                            ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                            ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                            ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                            ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                            ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                            ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                            ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
                            ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from (by
                              unfold nb090AlphaDummy797;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                            (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
                            (by
                              unfold nb090AlphaDummy798;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0837 v u h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from (by
                                unfold nb090AlphaDummy797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
                              (by
                                unfold nb090AlphaDummy798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                            ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                            ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                            ((nb090AlphaDummy819 A), (nb090AlphaDummy820 v u h)),
                            ((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)),
                            ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                            ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                            ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)),
                            ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                            ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                            ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                            ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                            ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                            ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                            ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                            ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
                            ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy793 A) from (by
                        unfold nb090AlphaDummy793;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0834 A) 0))))
                    (show (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy795 v u h) from (by
                        unfold nb090AlphaDummy795;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0835 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy794 A) from (by
                          unfold nb090AlphaDummy794;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0834 A) 1))))
                      (show (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy796 v u h) from
                        (by
                          unfold nb090AlphaDummy796;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0835 v u h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy819 A) from (by
                            unfold nb090AlphaDummy819;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0864 A) 0)))) (show
                          (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy820 v u h) from (by
                            unfold nb090AlphaDummy820;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0865 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy817 A) from (by
                              unfold nb090AlphaDummy817;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0862 A) 0)))) (show
                            (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy818 v u h) from
                            (by
                              unfold nb090AlphaDummy818;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0863 v u h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy786 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy788 v u h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy800 A) from (by
                                          unfold nb090AlphaDummy800;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0838 A) 1)))) (show
                                        (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy803 v u h) from (by
                                          unfold nb090AlphaDummy803;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0839 v u h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy799 A) from (by
          unfold nb090AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A) 0)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy802 v u h) from (by
          unfold nb090AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from (by
          unfold nb090AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A) 0)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy798 v u h) from (by
          unfold nb090AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy801 A),
        (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy819 A),
        (nb090AlphaDummy820 v u h)), ((nb090AlphaDummy817 A),
        (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy815 A),
        (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy801 A), (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy819 A),
        (nb090AlphaDummy820 v u h)), ((nb090AlphaDummy817 A),
        (nb090AlphaDummy818 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy815 A),
        (nb090AlphaDummy816 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                (by
                                  unfold nb090AlphaDummy797;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                                (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h)
                                from (by
                                  unfold nb090AlphaDummy798;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                              ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                              ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                              ((nb090AlphaDummy819 A), (nb090AlphaDummy820 v u h)),
                              ((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)),
                              ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                              ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                              ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)),
                              ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                              ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                              ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                              ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                              ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                              ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                              ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                              ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
                              ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from (by
                                unfold nb090AlphaDummy797;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                              (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
                              (by
                                unfold nb090AlphaDummy798;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                (by
                                  unfold nb090AlphaDummy797;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0836 A) 0)))) (show
                                (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h)
                                from (by
                                  unfold nb090AlphaDummy798;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0837 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                              ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                              ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                              ((nb090AlphaDummy819 A), (nb090AlphaDummy820 v u h)),
                              ((nb090AlphaDummy817 A), (nb090AlphaDummy818 v u h)),
                              ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                              ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                              ((nb090AlphaDummy815 A), (nb090AlphaDummy816 v u h)),
                              ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                              ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                              ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                              ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                              ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                              ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                              ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                              ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
                              ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0093`. -/
@[expose]
noncomputable def nb090SplitAlpha0093 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
        ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
        ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
        (synCun (synCphi (Class.cv (nb090AlphaDummy700 A))) (synCsn (synC0c))))
      (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
        (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h))) (synCsn (synC0c)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))).fv ∪
            ((synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))).fv) (by decide)) (freshVar_injective
          (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
            ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy753 A) from (by
                                    unfold nb090AlphaDummy753;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0794 A)
                                            0)))) (show (nb090AlphaDummy702 v u h) ≠
                                    (nb090AlphaDummy755 v u h) from (by
                                    unfold nb090AlphaDummy755;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy754 A) from
                                    (by
                                      unfold nb090AlphaDummy754;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0794 A)
                                              1)))) (show (nb090AlphaDummy702 v u h) ≠
                                      (nb090AlphaDummy756 v u h) from (by
                                      unfold nb090AlphaDummy756;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0795 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy700 A) ≠
                                        (nb090AlphaDummy825 A) from (by
                                        unfold nb090AlphaDummy825;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0878 A)
                                                0)))) (show (nb090AlphaDummy702 v u h) ≠
                                        (nb090AlphaDummy826 v u h) from (by
                                        unfold nb090AlphaDummy826;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0879 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy700 A) ≠
        (nb090AlphaDummy823 A) from (by
                                          unfold nb090AlphaDummy823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0876 A) 0)))) (show
                                        (nb090AlphaDummy702 v u h) ≠
        (nb090AlphaDummy824 v u h) from (by
                                          unfold nb090AlphaDummy824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0877 v u h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy700 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy702 v u h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy760 A) from (by
          unfold nb090AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  1)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy763 v u h) from
        (by
          unfold nb090AlphaDummy763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy759 A) from (by
          unfold nb090AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy762 v u h) from
        (by
          unfold nb090AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796
                    A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy758 v u h) from
        (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
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
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
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
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy753 A) from (by
                                    unfold nb090AlphaDummy753;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0794 A)
                                            0)))) (show (nb090AlphaDummy702 v u h) ≠
                                    (nb090AlphaDummy755 v u h) from (by
                                    unfold nb090AlphaDummy755;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy754 A) from
                                    (by
                                      unfold nb090AlphaDummy754;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0794 A)
                                              1)))) (show (nb090AlphaDummy702 v u h) ≠
                                      (nb090AlphaDummy756 v u h) from (by
                                      unfold nb090AlphaDummy756;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0795 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy700 A) ≠
                                        (nb090AlphaDummy825 A) from (by
                                        unfold nb090AlphaDummy825;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0878 A)
                                                0)))) (show (nb090AlphaDummy702 v u h) ≠
                                        (nb090AlphaDummy826 v u h) from (by
                                        unfold nb090AlphaDummy826;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0879 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy700 A) ≠
        (nb090AlphaDummy823 A) from (by
                                          unfold nb090AlphaDummy823;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0876 A) 0)))) (show
                                        (nb090AlphaDummy702 v u h) ≠
        (nb090AlphaDummy824 v u h) from (by
                                          unfold nb090AlphaDummy824;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0877 v u h) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy700 A))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv (nb090AlphaDummy702 v u h))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy760 A) from (by
          unfold nb090AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  1)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy763 v u h) from
        (by
          unfold nb090AlphaDummy763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy759 A) from (by
          unfold nb090AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy762 v u h) from
        (by
          unfold nb090AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v
                    u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796
                    A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy758 v u h) from
        (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC1c)
        (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
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
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synC0)
        (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here
        _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v
                    u
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _
        _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v
                    u
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
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
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synCnnc) (by simp only [fv_syn_cnnc])))))
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h) 0)))) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy825 A),
        (nb090AlphaDummy826 v u h)), ((nb090AlphaDummy823 A),
        (nb090AlphaDummy824 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))] (synCnnc)
                                        (by simp only [fv_syn_cnnc]))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.reflOfClosed
              [((nb090AlphaDummy823 A), (nb090AlphaDummy824 v u h)),
                ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
                ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                ((nb090AlphaDummy001 A), u),
                ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
              (synCcompl (synCsn (synC0c)))
              (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))

theorem nb090_compact_fv_empty_0640 (A : Class) :
    (nb090AlphaDummy827 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0641 (v : Var) :
    (nb090AlphaDummy828 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0642 (A : Class) :
    (nb090AlphaDummy829 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0643 (v : Var) :
    (nb090AlphaDummy830 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0644 (A : Class) :
    (nb090AlphaDummy832 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0645 (v : Var) :
    (nb090AlphaDummy834 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0646 (A : Class) :
    (nb090AlphaDummy831 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0647 (v : Var) :
    (nb090AlphaDummy833 v) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
