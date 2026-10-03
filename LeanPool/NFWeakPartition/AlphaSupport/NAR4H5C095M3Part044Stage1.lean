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

@[expose]
noncomputable def nb095_split_alpha_0097 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_833 D R S_cls E), (nb095_alpha_dummy_834 u S_cls E)),
        ((nb095_alpha_dummy_831 D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_829 D R S_cls E), (nb095_alpha_dummy_830 u S_cls E)),
        ((nb095_alpha_dummy_803 D R S_cls E), (nb095_alpha_dummy_804 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_833 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_833 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_834 u S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_834 u S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                      (nb095_alpha_dummy_807 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_807;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                    (nb095_alpha_dummy_802 u S_cls E) ≠ (nb095_alpha_dummy_809 u S_cls E) from
                    (by
                      unfold nb095_alpha_dummy_809;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                        (nb095_alpha_dummy_808 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_808;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_802 u S_cls E) ≠ (nb095_alpha_dummy_810 u S_cls E) from
                      (by
                        unfold nb095_alpha_dummy_810;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                          (nb095_alpha_dummy_833 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_833;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0882 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                          (nb095_alpha_dummy_834 u S_cls E) from (by
                          unfold nb095_alpha_dummy_834;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0883 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                            (nb095_alpha_dummy_831 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_831;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0880 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                            (nb095_alpha_dummy_832 u S_cls E) from (by
                            unfold nb095_alpha_dummy_832;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0881 u S_cls E)
                                    0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_807 D R S_cls E) ≠
                                        (nb095_alpha_dummy_814 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_814;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0856 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_809 u S_cls E) ≠
                                        (nb095_alpha_dummy_817 u S_cls E) from (by
                                        unfold nb095_alpha_dummy_817;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0857 u S_cls E) 1))))
                                    (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_813 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_813;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0856 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_816 u S_cls E) from (by
                                          unfold nb095_alpha_dummy_816;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0857 u S_cls E) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_807 D R S_cls E) ≠ (nb095_alpha_dummy_811 D R S_cls E) from (by
          unfold nb095_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_812 u S_cls E) from (by
          unfold nb095_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_815 D R S_cls E),
        (nb095_alpha_dummy_818 u S_cls E)), ((nb095_alpha_dummy_814 D R S_cls E),
        (nb095_alpha_dummy_817 u S_cls E)), ((nb095_alpha_dummy_813 D R S_cls E),
        (nb095_alpha_dummy_816 u S_cls E)), ((nb095_alpha_dummy_811 D R S_cls E),
        (nb095_alpha_dummy_812 u S_cls E)), ((nb095_alpha_dummy_807 D R S_cls E),
        (nb095_alpha_dummy_809 u S_cls E)), ((nb095_alpha_dummy_808 D R S_cls E),
        (nb095_alpha_dummy_810 u S_cls E)), ((nb095_alpha_dummy_833 D R S_cls E),
        (nb095_alpha_dummy_834 u S_cls E)), ((nb095_alpha_dummy_831 D R S_cls E),
        (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_815 D R S_cls E),
        (nb095_alpha_dummy_818 u S_cls E)), ((nb095_alpha_dummy_814 D R S_cls E),
        (nb095_alpha_dummy_817 u S_cls E)), ((nb095_alpha_dummy_813 D R S_cls E),
        (nb095_alpha_dummy_816 u S_cls E)), ((nb095_alpha_dummy_811 D R S_cls E),
        (nb095_alpha_dummy_812 u S_cls E)), ((nb095_alpha_dummy_807 D R S_cls E),
        (nb095_alpha_dummy_809 u S_cls E)), ((nb095_alpha_dummy_808 D R S_cls E),
        (nb095_alpha_dummy_810 u S_cls E)), ((nb095_alpha_dummy_833 D R S_cls E),
        (nb095_alpha_dummy_834 u S_cls E)), ((nb095_alpha_dummy_831 D R S_cls E),
        (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_827 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_827 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_807 D R S_cls E) ≠
                                (nb095_alpha_dummy_811 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_809 u S_cls E) ≠
                                (nb095_alpha_dummy_812 u S_cls E) from (by
                                unfold nb095_alpha_dummy_812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_811 D R S_cls E),
                              (nb095_alpha_dummy_812 u S_cls E)),
                            ((nb095_alpha_dummy_807 D R S_cls E),
                              (nb095_alpha_dummy_809 u S_cls E)),
                            ((nb095_alpha_dummy_808 D R S_cls E),
                              (nb095_alpha_dummy_810 u S_cls E)),
                            ((nb095_alpha_dummy_833 D R S_cls E),
                              (nb095_alpha_dummy_834 u S_cls E)),
                            ((nb095_alpha_dummy_831 D R S_cls E),
                              (nb095_alpha_dummy_832 u S_cls E)),
                            ((nb095_alpha_dummy_800 D R S_cls E),
                              (nb095_alpha_dummy_802 u S_cls E)),
                            ((nb095_alpha_dummy_799 D R S_cls E),
                              (nb095_alpha_dummy_801 u S_cls E)),
                            ((nb095_alpha_dummy_829 D R S_cls E),
                              (nb095_alpha_dummy_830 u S_cls E)),
                            ((nb095_alpha_dummy_803 D R S_cls E),
                              (nb095_alpha_dummy_804 u S_cls E)),
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
                              (nb095_alpha_dummy_811 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_811;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0854 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
                              (nb095_alpha_dummy_812 u S_cls E) from (by
                              unfold nb095_alpha_dummy_812;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                      0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_807 D R S_cls E) ≠
                                (nb095_alpha_dummy_811 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_809 u S_cls E) ≠
                                (nb095_alpha_dummy_812 u S_cls E) from (by
                                unfold nb095_alpha_dummy_812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_811 D R S_cls E),
                              (nb095_alpha_dummy_812 u S_cls E)),
                            ((nb095_alpha_dummy_807 D R S_cls E),
                              (nb095_alpha_dummy_809 u S_cls E)),
                            ((nb095_alpha_dummy_808 D R S_cls E),
                              (nb095_alpha_dummy_810 u S_cls E)),
                            ((nb095_alpha_dummy_833 D R S_cls E),
                              (nb095_alpha_dummy_834 u S_cls E)),
                            ((nb095_alpha_dummy_831 D R S_cls E),
                              (nb095_alpha_dummy_832 u S_cls E)),
                            ((nb095_alpha_dummy_800 D R S_cls E),
                              (nb095_alpha_dummy_802 u S_cls E)),
                            ((nb095_alpha_dummy_799 D R S_cls E),
                              (nb095_alpha_dummy_801 u S_cls E)),
                            ((nb095_alpha_dummy_829 D R S_cls E),
                              (nb095_alpha_dummy_830 u S_cls E)),
                            ((nb095_alpha_dummy_803 D R S_cls E),
                              (nb095_alpha_dummy_804 u S_cls E)),
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                        (nb095_alpha_dummy_807 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_807;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_802 u S_cls E) ≠ (nb095_alpha_dummy_809 u S_cls E) from
                      (by
                        unfold nb095_alpha_dummy_809;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                          (nb095_alpha_dummy_808 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_808;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E)
                                  1)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                          (nb095_alpha_dummy_810 u S_cls E) from (by
                          unfold nb095_alpha_dummy_810;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                            (nb095_alpha_dummy_833 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_833;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0882 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                            (nb095_alpha_dummy_834 u S_cls E) from (by
                            unfold nb095_alpha_dummy_834;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0883 u S_cls E)
                                    0)))) (TAlphaVar.there (show
                            (nb095_alpha_dummy_800 D R S_cls E) ≠
                              (nb095_alpha_dummy_831 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_831;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0880 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                              (nb095_alpha_dummy_832 u S_cls E) from (by
                              unfold nb095_alpha_dummy_832;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0881 u S_cls E)
                                      0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_814 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_814;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0856 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_817 u S_cls E) from (by
                                          unfold nb095_alpha_dummy_817;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0857 u S_cls E) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_807 D R S_cls E) ≠ (nb095_alpha_dummy_813 D R S_cls E) from (by
          unfold nb095_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_816 u S_cls E) from (by
          unfold nb095_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_811 D R S_cls E) from (by
          unfold nb095_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_812 u S_cls E) from (by
          unfold nb095_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_815 D R S_cls E),
        (nb095_alpha_dummy_818 u S_cls E)), ((nb095_alpha_dummy_814 D R S_cls E),
        (nb095_alpha_dummy_817 u S_cls E)), ((nb095_alpha_dummy_813 D R S_cls E),
        (nb095_alpha_dummy_816 u S_cls E)), ((nb095_alpha_dummy_811 D R S_cls E),
        (nb095_alpha_dummy_812 u S_cls E)), ((nb095_alpha_dummy_807 D R S_cls E),
        (nb095_alpha_dummy_809 u S_cls E)), ((nb095_alpha_dummy_808 D R S_cls E),
        (nb095_alpha_dummy_810 u S_cls E)), ((nb095_alpha_dummy_833 D R S_cls E),
        (nb095_alpha_dummy_834 u S_cls E)), ((nb095_alpha_dummy_831 D R S_cls E),
        (nb095_alpha_dummy_832 u S_cls E)), ((nb095_alpha_dummy_800 D R S_cls E),
        (nb095_alpha_dummy_802 u S_cls E)), ((nb095_alpha_dummy_799 D R S_cls E),
        (nb095_alpha_dummy_801 u S_cls E)), ((nb095_alpha_dummy_829 D R S_cls E),
        (nb095_alpha_dummy_830 u S_cls E)), ((nb095_alpha_dummy_803 D R S_cls E),
        (nb095_alpha_dummy_804 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_815 D R S_cls E), (nb095_alpha_dummy_818 u S_cls E)),
        ((nb095_alpha_dummy_814 D R S_cls E), (nb095_alpha_dummy_817 u S_cls E)),
        ((nb095_alpha_dummy_813 D R S_cls E), (nb095_alpha_dummy_816 u S_cls E)),
        ((nb095_alpha_dummy_811 D R S_cls E), (nb095_alpha_dummy_812 u S_cls E)),
        ((nb095_alpha_dummy_807 D R S_cls E), (nb095_alpha_dummy_809 u S_cls E)),
        ((nb095_alpha_dummy_808 D R S_cls E), (nb095_alpha_dummy_810 u S_cls E)),
        ((nb095_alpha_dummy_833 D R S_cls E), (nb095_alpha_dummy_834 u S_cls E)),
        ((nb095_alpha_dummy_831 D R S_cls E), (nb095_alpha_dummy_832 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_829 D R S_cls E), (nb095_alpha_dummy_830 u S_cls E)),
        ((nb095_alpha_dummy_803 D R S_cls E), (nb095_alpha_dummy_804 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_827 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_827 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824 u
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_807 D R S_cls E) ≠
                                  (nb095_alpha_dummy_811 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_811;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_809 u S_cls E) ≠
                                  (nb095_alpha_dummy_812 u S_cls E) from (by
                                  unfold nb095_alpha_dummy_812;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0855 u S_cls E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_811 D R S_cls E),
                                (nb095_alpha_dummy_812 u S_cls E)),
                              ((nb095_alpha_dummy_807 D R S_cls E),
                                (nb095_alpha_dummy_809 u S_cls E)),
                              ((nb095_alpha_dummy_808 D R S_cls E),
                                (nb095_alpha_dummy_810 u S_cls E)),
                              ((nb095_alpha_dummy_833 D R S_cls E),
                                (nb095_alpha_dummy_834 u S_cls E)),
                              ((nb095_alpha_dummy_831 D R S_cls E),
                                (nb095_alpha_dummy_832 u S_cls E)),
                              ((nb095_alpha_dummy_800 D R S_cls E),
                                (nb095_alpha_dummy_802 u S_cls E)),
                              ((nb095_alpha_dummy_799 D R S_cls E),
                                (nb095_alpha_dummy_801 u S_cls E)),
                              ((nb095_alpha_dummy_829 D R S_cls E),
                                (nb095_alpha_dummy_830 u S_cls E)),
                              ((nb095_alpha_dummy_803 D R S_cls E),
                                (nb095_alpha_dummy_804 u S_cls E)),
                              ((nb095_alpha_dummy_794 D R S_cls E),
                                (nb095_alpha_dummy_796 u S_cls E)),
                              ((nb095_alpha_dummy_793 D R S_cls E),
                                (nb095_alpha_dummy_795 u S_cls E)),
                              ((nb095_alpha_dummy_797 D R S_cls E),
                                (nb095_alpha_dummy_798 u S_cls E)),
                              ((nb095_alpha_dummy_791 D R S_cls E),
                                (nb095_alpha_dummy_792 u S_cls E)),
                              ((nb095_alpha_dummy_789 D R S_cls E),
                                (nb095_alpha_dummy_790 u S_cls E)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_807 D R S_cls E) ≠
                                (nb095_alpha_dummy_811 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_811;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_809 u S_cls E) ≠
                                (nb095_alpha_dummy_812 u S_cls E) from (by
                                unfold nb095_alpha_dummy_812;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0855 u S_cls E)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_807 D R S_cls E) ≠
                                  (nb095_alpha_dummy_811 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_811;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0854 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_809 u S_cls E) ≠
                                  (nb095_alpha_dummy_812 u S_cls E) from (by
                                  unfold nb095_alpha_dummy_812;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0855 u S_cls E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_811 D R S_cls E),
                                (nb095_alpha_dummy_812 u S_cls E)),
                              ((nb095_alpha_dummy_807 D R S_cls E),
                                (nb095_alpha_dummy_809 u S_cls E)),
                              ((nb095_alpha_dummy_808 D R S_cls E),
                                (nb095_alpha_dummy_810 u S_cls E)),
                              ((nb095_alpha_dummy_833 D R S_cls E),
                                (nb095_alpha_dummy_834 u S_cls E)),
                              ((nb095_alpha_dummy_831 D R S_cls E),
                                (nb095_alpha_dummy_832 u S_cls E)),
                              ((nb095_alpha_dummy_800 D R S_cls E),
                                (nb095_alpha_dummy_802 u S_cls E)),
                              ((nb095_alpha_dummy_799 D R S_cls E),
                                (nb095_alpha_dummy_801 u S_cls E)),
                              ((nb095_alpha_dummy_829 D R S_cls E),
                                (nb095_alpha_dummy_830 u S_cls E)),
                              ((nb095_alpha_dummy_803 D R S_cls E),
                                (nb095_alpha_dummy_804 u S_cls E)),
                              ((nb095_alpha_dummy_794 D R S_cls E),
                                (nb095_alpha_dummy_796 u S_cls E)),
                              ((nb095_alpha_dummy_793 D R S_cls E),
                                (nb095_alpha_dummy_795 u S_cls E)),
                              ((nb095_alpha_dummy_797 D R S_cls E),
                                (nb095_alpha_dummy_798 u S_cls E)),
                              ((nb095_alpha_dummy_791 D R S_cls E),
                                (nb095_alpha_dummy_792 u S_cls E)),
                              ((nb095_alpha_dummy_789 D R S_cls E),
                                (nb095_alpha_dummy_790 u S_cls E)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb095_focused_notmem_0080 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0081 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        1 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0082 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0083 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0084 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_797 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
            ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0085 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_798 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
            ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0086 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_791 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0087 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_792 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        ((S_cls).fv ∪ ((syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u)))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0088 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_789 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0089 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_790 u S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((syn_cnin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv)
        0 ∉
      E.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin S_cls
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0090 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
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
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0091 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
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
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0092 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                            (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
              ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
            ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
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
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0093 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∉ E.fv :=
  by
  change
    freshVar
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                          (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                    (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv)
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
      (syn_cxp (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
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
      [((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_337 D R S_cls E)
      (nb095_alpha_dummy_338 u S_cls E) (nb095_focused_notmem_0021 D R S_cls E)
      (nb095_focused_notmem_0022 u S_cls E)
      (TEnvFresh.consFresh (nb095_alpha_dummy_335 D R S_cls E)
        (nb095_alpha_dummy_336 u S_cls E) (nb095_focused_notmem_0023 D R S_cls E)
        (nb095_focused_notmem_0024 u S_cls E)
        (TEnvFresh.consFresh (nb095_alpha_dummy_794 D R S_cls E)
          (nb095_alpha_dummy_796 u S_cls E) (nb095_focused_notmem_0080 D R S_cls E)
          (nb095_focused_notmem_0081 u S_cls E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_793 D R S_cls E)
            (nb095_alpha_dummy_795 u S_cls E) (nb095_focused_notmem_0082 D R S_cls E)
            (nb095_focused_notmem_0083 u S_cls E)
            (TEnvFresh.consFresh (nb095_alpha_dummy_797 D R S_cls E)
              (nb095_alpha_dummy_798 u S_cls E) (nb095_focused_notmem_0084 D R S_cls E)
              (nb095_focused_notmem_0085 u S_cls E)
              (TEnvFresh.consFresh (nb095_alpha_dummy_791 D R S_cls E)
                (nb095_alpha_dummy_792 u S_cls E) (nb095_focused_notmem_0086 D R S_cls E)
                (nb095_focused_notmem_0087 u S_cls E)
                (TEnvFresh.consFresh (nb095_alpha_dummy_789 D R S_cls E)
                  (nb095_alpha_dummy_790 u S_cls E) (nb095_focused_notmem_0088 D R S_cls E)
                  (nb095_focused_notmem_0089 u S_cls E)
                  (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
                    (nb095_alpha_dummy_006 x u D R S_cls f E)
                    (nb095_focused_notmem_0090 D R S_cls E)
                    (nb095_focused_notmem_0091 x u D R S_cls f E)
                    (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
                      (nb095_alpha_dummy_005 x u D R S_cls f E)
                      (nb095_focused_notmem_0092 D R S_cls E)
                      (nb095_focused_notmem_0093 x u D R S_cls f E)
                      (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
                        (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
                        (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                          (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
                          (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                            (nb095_focused_notmem_0004 D R S_cls E) dv_E_f
                            (TEnvFresh.nil E.fv)))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
