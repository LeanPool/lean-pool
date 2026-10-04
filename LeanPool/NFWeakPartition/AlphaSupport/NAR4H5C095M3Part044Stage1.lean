/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part043

/-! NF weak partition development: NAR4H5C095M3Part044. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0097`. -/
@[expose]
noncomputable def nb095SplitAlpha0097 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy833 D R S_cls E), (nb095AlphaDummy834 u S_cls E)),
        ((nb095AlphaDummy831 D R S_cls E), (nb095AlphaDummy832 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy829 D R S_cls E), (nb095AlphaDummy830 u S_cls E)),
        ((nb095AlphaDummy803 D R S_cls E), (nb095AlphaDummy804 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy833 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy833 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy834 u S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy834 u S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                      (nb095AlphaDummy807 D R S_cls E) from (by
                      unfold nb095AlphaDummy807;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                    (nb095AlphaDummy802 u S_cls E) ≠ (nb095AlphaDummy809 u S_cls E) from
                    (by
                      unfold nb095AlphaDummy809;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                        (nb095AlphaDummy808 D R S_cls E) from (by
                        unfold nb095AlphaDummy808;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy802 u S_cls E) ≠ (nb095AlphaDummy810 u S_cls E) from
                      (by
                        unfold nb095AlphaDummy810;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                          (nb095AlphaDummy833 D R S_cls E) from (by
                          unfold nb095AlphaDummy833;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0882 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                          (nb095AlphaDummy834 u S_cls E) from (by
                          unfold nb095AlphaDummy834;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0883 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                            (nb095AlphaDummy831 D R S_cls E) from (by
                            unfold nb095AlphaDummy831;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0880 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                            (nb095AlphaDummy832 u S_cls E) from (by
                            unfold nb095AlphaDummy832;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0881 u S_cls E)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy807 D R S_cls E) ≠
                                        (nb095AlphaDummy814 D R S_cls E) from (by
                                        unfold nb095AlphaDummy814;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0856 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy809 u S_cls E) ≠
                                        (nb095AlphaDummy817 u S_cls E) from (by
                                        unfold nb095AlphaDummy817;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0857 u S_cls E) 1))))
                                    (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy813 D R S_cls E) from (by
                                          unfold nb095AlphaDummy813;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0856 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy816 u S_cls E) from (by
                                          unfold nb095AlphaDummy816;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0857 u S_cls E) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy807 D R S_cls E) ≠ (nb095AlphaDummy811 D R S_cls E) from (by
          unfold nb095AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy812 u S_cls E) from (by
          unfold nb095AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy815 D R S_cls E),
        (nb095AlphaDummy818 u S_cls E)), ((nb095AlphaDummy814 D R S_cls E),
        (nb095AlphaDummy817 u S_cls E)), ((nb095AlphaDummy813 D R S_cls E),
        (nb095AlphaDummy816 u S_cls E)), ((nb095AlphaDummy811 D R S_cls E),
        (nb095AlphaDummy812 u S_cls E)), ((nb095AlphaDummy807 D R S_cls E),
        (nb095AlphaDummy809 u S_cls E)), ((nb095AlphaDummy808 D R S_cls E),
        (nb095AlphaDummy810 u S_cls E)), ((nb095AlphaDummy833 D R S_cls E),
        (nb095AlphaDummy834 u S_cls E)), ((nb095AlphaDummy831 D R S_cls E),
        (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy815 D R S_cls E),
        (nb095AlphaDummy818 u S_cls E)), ((nb095AlphaDummy814 D R S_cls E),
        (nb095AlphaDummy817 u S_cls E)), ((nb095AlphaDummy813 D R S_cls E),
        (nb095AlphaDummy816 u S_cls E)), ((nb095AlphaDummy811 D R S_cls E),
        (nb095AlphaDummy812 u S_cls E)), ((nb095AlphaDummy807 D R S_cls E),
        (nb095AlphaDummy809 u S_cls E)), ((nb095AlphaDummy808 D R S_cls E),
        (nb095AlphaDummy810 u S_cls E)), ((nb095AlphaDummy833 D R S_cls E),
        (nb095AlphaDummy834 u S_cls E)), ((nb095AlphaDummy831 D R S_cls E),
        (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy827 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy827 D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy807 D R S_cls E) ≠
                                (nb095AlphaDummy811 D R S_cls E) from (by
                                unfold nb095AlphaDummy811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy809 u S_cls E) ≠
                                (nb095AlphaDummy812 u S_cls E) from (by
                                unfold nb095AlphaDummy812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed [((nb095AlphaDummy811 D R S_cls E),
                              (nb095AlphaDummy812 u S_cls E)),
                            ((nb095AlphaDummy807 D R S_cls E),
                              (nb095AlphaDummy809 u S_cls E)),
                            ((nb095AlphaDummy808 D R S_cls E),
                              (nb095AlphaDummy810 u S_cls E)),
                            ((nb095AlphaDummy833 D R S_cls E),
                              (nb095AlphaDummy834 u S_cls E)),
                            ((nb095AlphaDummy831 D R S_cls E),
                              (nb095AlphaDummy832 u S_cls E)),
                            ((nb095AlphaDummy800 D R S_cls E),
                              (nb095AlphaDummy802 u S_cls E)),
                            ((nb095AlphaDummy799 D R S_cls E),
                              (nb095AlphaDummy801 u S_cls E)),
                            ((nb095AlphaDummy829 D R S_cls E),
                              (nb095AlphaDummy830 u S_cls E)),
                            ((nb095AlphaDummy803 D R S_cls E),
                              (nb095AlphaDummy804 u S_cls E)),
                            ((nb095AlphaDummy794 D R S_cls E),
                              (nb095AlphaDummy796 u S_cls E)),
                            ((nb095AlphaDummy793 D R S_cls E),
                              (nb095AlphaDummy795 u S_cls E)),
                            ((nb095AlphaDummy797 D R S_cls E),
                              (nb095AlphaDummy798 u S_cls E)),
                            ((nb095AlphaDummy791 D R S_cls E),
                              (nb095AlphaDummy792 u S_cls E)),
                            ((nb095AlphaDummy789 D R S_cls E),
                              (nb095AlphaDummy790 u S_cls E)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
                              (nb095AlphaDummy811 D R S_cls E) from (by
                              unfold nb095AlphaDummy811;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0854 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
                              (nb095AlphaDummy812 u S_cls E) from (by
                              unfold nb095AlphaDummy812;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                      0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy807 D R S_cls E) ≠
                                (nb095AlphaDummy811 D R S_cls E) from (by
                                unfold nb095AlphaDummy811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy809 u S_cls E) ≠
                                (nb095AlphaDummy812 u S_cls E) from (by
                                unfold nb095AlphaDummy812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed [((nb095AlphaDummy811 D R S_cls E),
                              (nb095AlphaDummy812 u S_cls E)),
                            ((nb095AlphaDummy807 D R S_cls E),
                              (nb095AlphaDummy809 u S_cls E)),
                            ((nb095AlphaDummy808 D R S_cls E),
                              (nb095AlphaDummy810 u S_cls E)),
                            ((nb095AlphaDummy833 D R S_cls E),
                              (nb095AlphaDummy834 u S_cls E)),
                            ((nb095AlphaDummy831 D R S_cls E),
                              (nb095AlphaDummy832 u S_cls E)),
                            ((nb095AlphaDummy800 D R S_cls E),
                              (nb095AlphaDummy802 u S_cls E)),
                            ((nb095AlphaDummy799 D R S_cls E),
                              (nb095AlphaDummy801 u S_cls E)),
                            ((nb095AlphaDummy829 D R S_cls E),
                              (nb095AlphaDummy830 u S_cls E)),
                            ((nb095AlphaDummy803 D R S_cls E),
                              (nb095AlphaDummy804 u S_cls E)),
                            ((nb095AlphaDummy794 D R S_cls E),
                              (nb095AlphaDummy796 u S_cls E)),
                            ((nb095AlphaDummy793 D R S_cls E),
                              (nb095AlphaDummy795 u S_cls E)),
                            ((nb095AlphaDummy797 D R S_cls E),
                              (nb095AlphaDummy798 u S_cls E)),
                            ((nb095AlphaDummy791 D R S_cls E),
                              (nb095AlphaDummy792 u S_cls E)),
                            ((nb095AlphaDummy789 D R S_cls E),
                              (nb095AlphaDummy790 u S_cls E)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                        (nb095AlphaDummy807 D R S_cls E) from (by
                        unfold nb095AlphaDummy807;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy802 u S_cls E) ≠ (nb095AlphaDummy809 u S_cls E) from
                      (by
                        unfold nb095AlphaDummy809;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                          (nb095AlphaDummy808 D R S_cls E) from (by
                          unfold nb095AlphaDummy808;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E)
                                  1)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                          (nb095AlphaDummy810 u S_cls E) from (by
                          unfold nb095AlphaDummy810;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                            (nb095AlphaDummy833 D R S_cls E) from (by
                            unfold nb095AlphaDummy833;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0882 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                            (nb095AlphaDummy834 u S_cls E) from (by
                            unfold nb095AlphaDummy834;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0883 u S_cls E)
                                    0)))) (TAlphaVar.there (show
                            (nb095AlphaDummy800 D R S_cls E) ≠
                              (nb095AlphaDummy831 D R S_cls E) from (by
                              unfold nb095AlphaDummy831;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0880 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                              (nb095AlphaDummy832 u S_cls E) from (by
                              unfold nb095AlphaDummy832;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0881 u S_cls E)
                                      0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy814 D R S_cls E) from (by
                                          unfold nb095AlphaDummy814;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0856 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy817 u S_cls E) from (by
                                          unfold nb095AlphaDummy817;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0857 u S_cls E) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy807 D R S_cls E) ≠ (nb095AlphaDummy813 D R S_cls E) from (by
          unfold nb095AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy816 u S_cls E) from (by
          unfold nb095AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy811 D R S_cls E) from (by
          unfold nb095AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy812 u S_cls E) from (by
          unfold nb095AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy815 D R S_cls E),
        (nb095AlphaDummy818 u S_cls E)), ((nb095AlphaDummy814 D R S_cls E),
        (nb095AlphaDummy817 u S_cls E)), ((nb095AlphaDummy813 D R S_cls E),
        (nb095AlphaDummy816 u S_cls E)), ((nb095AlphaDummy811 D R S_cls E),
        (nb095AlphaDummy812 u S_cls E)), ((nb095AlphaDummy807 D R S_cls E),
        (nb095AlphaDummy809 u S_cls E)), ((nb095AlphaDummy808 D R S_cls E),
        (nb095AlphaDummy810 u S_cls E)), ((nb095AlphaDummy833 D R S_cls E),
        (nb095AlphaDummy834 u S_cls E)), ((nb095AlphaDummy831 D R S_cls E),
        (nb095AlphaDummy832 u S_cls E)), ((nb095AlphaDummy800 D R S_cls E),
        (nb095AlphaDummy802 u S_cls E)), ((nb095AlphaDummy799 D R S_cls E),
        (nb095AlphaDummy801 u S_cls E)), ((nb095AlphaDummy829 D R S_cls E),
        (nb095AlphaDummy830 u S_cls E)), ((nb095AlphaDummy803 D R S_cls E),
        (nb095AlphaDummy804 u S_cls E)), ((nb095AlphaDummy794 D R S_cls E),
        (nb095AlphaDummy796 u S_cls E)), ((nb095AlphaDummy793 D R S_cls E),
        (nb095AlphaDummy795 u S_cls E)), ((nb095AlphaDummy797 D R S_cls E),
        (nb095AlphaDummy798 u S_cls E)), ((nb095AlphaDummy791 D R S_cls E),
        (nb095AlphaDummy792 u S_cls E)), ((nb095AlphaDummy789 D R S_cls E),
        (nb095AlphaDummy790 u S_cls E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy815 D R S_cls E), (nb095AlphaDummy818 u S_cls E)),
        ((nb095AlphaDummy814 D R S_cls E), (nb095AlphaDummy817 u S_cls E)),
        ((nb095AlphaDummy813 D R S_cls E), (nb095AlphaDummy816 u S_cls E)),
        ((nb095AlphaDummy811 D R S_cls E), (nb095AlphaDummy812 u S_cls E)),
        ((nb095AlphaDummy807 D R S_cls E), (nb095AlphaDummy809 u S_cls E)),
        ((nb095AlphaDummy808 D R S_cls E), (nb095AlphaDummy810 u S_cls E)),
        ((nb095AlphaDummy833 D R S_cls E), (nb095AlphaDummy834 u S_cls E)),
        ((nb095AlphaDummy831 D R S_cls E), (nb095AlphaDummy832 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy829 D R S_cls E), (nb095AlphaDummy830 u S_cls E)),
        ((nb095AlphaDummy803 D R S_cls E), (nb095AlphaDummy804 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy827 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy827 D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824 u
        S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy807 D R S_cls E) ≠
                                  (nb095AlphaDummy811 D R S_cls E) from (by
                                  unfold nb095AlphaDummy811;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy809 u S_cls E) ≠
                                  (nb095AlphaDummy812 u S_cls E) from (by
                                  unfold nb095AlphaDummy812;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0855 u S_cls E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy811 D R S_cls E),
                                (nb095AlphaDummy812 u S_cls E)),
                              ((nb095AlphaDummy807 D R S_cls E),
                                (nb095AlphaDummy809 u S_cls E)),
                              ((nb095AlphaDummy808 D R S_cls E),
                                (nb095AlphaDummy810 u S_cls E)),
                              ((nb095AlphaDummy833 D R S_cls E),
                                (nb095AlphaDummy834 u S_cls E)),
                              ((nb095AlphaDummy831 D R S_cls E),
                                (nb095AlphaDummy832 u S_cls E)),
                              ((nb095AlphaDummy800 D R S_cls E),
                                (nb095AlphaDummy802 u S_cls E)),
                              ((nb095AlphaDummy799 D R S_cls E),
                                (nb095AlphaDummy801 u S_cls E)),
                              ((nb095AlphaDummy829 D R S_cls E),
                                (nb095AlphaDummy830 u S_cls E)),
                              ((nb095AlphaDummy803 D R S_cls E),
                                (nb095AlphaDummy804 u S_cls E)),
                              ((nb095AlphaDummy794 D R S_cls E),
                                (nb095AlphaDummy796 u S_cls E)),
                              ((nb095AlphaDummy793 D R S_cls E),
                                (nb095AlphaDummy795 u S_cls E)),
                              ((nb095AlphaDummy797 D R S_cls E),
                                (nb095AlphaDummy798 u S_cls E)),
                              ((nb095AlphaDummy791 D R S_cls E),
                                (nb095AlphaDummy792 u S_cls E)),
                              ((nb095AlphaDummy789 D R S_cls E),
                                (nb095AlphaDummy790 u S_cls E)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy807 D R S_cls E) ≠
                                (nb095AlphaDummy811 D R S_cls E) from (by
                                unfold nb095AlphaDummy811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy809 u S_cls E) ≠
                                (nb095AlphaDummy812 u S_cls E) from (by
                                unfold nb095AlphaDummy812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy807 D R S_cls E) ≠
                                  (nb095AlphaDummy811 D R S_cls E) from (by
                                  unfold nb095AlphaDummy811;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy809 u S_cls E) ≠
                                  (nb095AlphaDummy812 u S_cls E) from (by
                                  unfold nb095AlphaDummy812;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0855 u S_cls E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy811 D R S_cls E),
                                (nb095AlphaDummy812 u S_cls E)),
                              ((nb095AlphaDummy807 D R S_cls E),
                                (nb095AlphaDummy809 u S_cls E)),
                              ((nb095AlphaDummy808 D R S_cls E),
                                (nb095AlphaDummy810 u S_cls E)),
                              ((nb095AlphaDummy833 D R S_cls E),
                                (nb095AlphaDummy834 u S_cls E)),
                              ((nb095AlphaDummy831 D R S_cls E),
                                (nb095AlphaDummy832 u S_cls E)),
                              ((nb095AlphaDummy800 D R S_cls E),
                                (nb095AlphaDummy802 u S_cls E)),
                              ((nb095AlphaDummy799 D R S_cls E),
                                (nb095AlphaDummy801 u S_cls E)),
                              ((nb095AlphaDummy829 D R S_cls E),
                                (nb095AlphaDummy830 u S_cls E)),
                              ((nb095AlphaDummy803 D R S_cls E),
                                (nb095AlphaDummy804 u S_cls E)),
                              ((nb095AlphaDummy794 D R S_cls E),
                                (nb095AlphaDummy796 u S_cls E)),
                              ((nb095AlphaDummy793 D R S_cls E),
                                (nb095AlphaDummy795 u S_cls E)),
                              ((nb095AlphaDummy797 D R S_cls E),
                                (nb095AlphaDummy798 u S_cls E)),
                              ((nb095AlphaDummy791 D R S_cls E),
                                (nb095AlphaDummy792 u S_cls E)),
                              ((nb095AlphaDummy789 D R S_cls E),
                                (nb095AlphaDummy790 u S_cls E)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb095_focused_notmem_0080 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0081 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0082 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0083 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0084 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy797 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
            ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
              (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
      (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095AlphaDummy793 D R S_cls E))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0085 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy798 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
            ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
              (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095AlphaDummy795 u S_cls E))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0086 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy791 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0087 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy792 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0088 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy789 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0089 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy790 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((synCnin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                    (synCsn (Class.cv u))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0090 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn
                            (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
              ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0091 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                      (synCin D (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0092 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn
                            (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
              ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
            ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0093 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095AlphaDummy005 x u D R S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                      (synCin D (synCima (synCcnv (synCdif R (synCid)))
                          (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                    (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                        (synCsn (Class.cv u))))))).fv ∪ ((synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin S_cls
      (synCxp (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))) (synCin E
          (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
      (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu


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

theorem nb095_compact_envfresh_0336 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TEnvFresh
      [((nb095AlphaDummy337 D R S_cls E), (nb095AlphaDummy338 u S_cls E)),
        ((nb095AlphaDummy335 D R S_cls E), (nb095AlphaDummy336 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy337 D R S_cls E)
      (nb095AlphaDummy338 u S_cls E) (nb095_focused_notmem_0021 D R S_cls E)
      (nb095_focused_notmem_0022 u S_cls E)
      (TEnvFresh.consFresh (nb095AlphaDummy335 D R S_cls E)
        (nb095AlphaDummy336 u S_cls E) (nb095_focused_notmem_0023 D R S_cls E)
        (nb095_focused_notmem_0024 u S_cls E)
        (TEnvFresh.consFresh (nb095AlphaDummy794 D R S_cls E)
          (nb095AlphaDummy796 u S_cls E) (nb095_focused_notmem_0080 D R S_cls E)
          (nb095_focused_notmem_0081 u S_cls E)
          (TEnvFresh.consFresh (nb095AlphaDummy793 D R S_cls E)
            (nb095AlphaDummy795 u S_cls E) (nb095_focused_notmem_0082 D R S_cls E)
            (nb095_focused_notmem_0083 u S_cls E)
            (TEnvFresh.consFresh (nb095AlphaDummy797 D R S_cls E)
              (nb095AlphaDummy798 u S_cls E) (nb095_focused_notmem_0084 D R S_cls E)
              (nb095_focused_notmem_0085 u S_cls E)
              (TEnvFresh.consFresh (nb095AlphaDummy791 D R S_cls E)
                (nb095AlphaDummy792 u S_cls E) (nb095_focused_notmem_0086 D R S_cls E)
                (nb095_focused_notmem_0087 u S_cls E)
                (TEnvFresh.consFresh (nb095AlphaDummy789 D R S_cls E)
                  (nb095AlphaDummy790 u S_cls E) (nb095_focused_notmem_0088 D R S_cls E)
                  (nb095_focused_notmem_0089 u S_cls E)
                  (TEnvFresh.consFresh (nb095AlphaDummy004 D R S_cls E)
                    (nb095AlphaDummy006 x u D R S_cls f E)
                    (nb095_focused_notmem_0090 D R S_cls E)
                    (nb095_focused_notmem_0091 x u D R S_cls f E)
                    (TEnvFresh.consFresh (nb095AlphaDummy003 D R S_cls E)
                      (nb095AlphaDummy005 x u D R S_cls f E)
                      (nb095_focused_notmem_0092 D R S_cls E)
                      (nb095_focused_notmem_0093 x u D R S_cls f E)
                      (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
                        (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
                        (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                          (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
                          (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                            (nb095_focused_notmem_0004 D R S_cls E) dv_E_f
                            (TEnvFresh.nil E.fv)))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
