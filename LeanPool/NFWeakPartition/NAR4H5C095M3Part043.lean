/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4H5C095M3Part043Block001


/-! NF weak partition development: NAR4H5C095M3Part043. -/


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
noncomputable def nb095_split_alpha_0096 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_805 D R S_cls E), (nb095_alpha_dummy_806 u S_cls E)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_805 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_805 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_806 u S_cls E))
          (Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_806 u S_cls E))
            (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_795 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                      (nb095_alpha_dummy_800 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_800;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1)))) (show
                    (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from
                    (by
                      unfold nb095_alpha_dummy_802;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                        (nb095_alpha_dummy_799 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_799;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_801 u S_cls E) from
                      (by
                        unfold nb095_alpha_dummy_801;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                          (nb095_alpha_dummy_805 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_805;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0850 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_795 u S_cls E) ≠
                          (nb095_alpha_dummy_806 u S_cls E) from (by
                          unfold nb095_alpha_dummy_806;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0851 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                            (nb095_alpha_dummy_803 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_803;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0847 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_795 u S_cls E) ≠
                            (nb095_alpha_dummy_804 u S_cls E) from (by
                            unfold nb095_alpha_dummy_804;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0849 u S_cls E)
                                    0)))) (TAlphaVar.there (freshVar_injective (((syn_cin E
                                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn
                                      (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪
                              ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (syn_csn (Class.cv
                                        (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((syn_cin E
                                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
                                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                    (syn_csn (Class.cv u))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_800 D R S_cls E) ≠
                              (nb095_alpha_dummy_807 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_807;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_802 u S_cls E) ≠
                              (nb095_alpha_dummy_809 u S_cls E) from (by
                              unfold nb095_alpha_dummy_809;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                      0)))) (TAlphaVar.there (show
                              (nb095_alpha_dummy_800 D R S_cls E) ≠
                                (nb095_alpha_dummy_808 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_808;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_802 u S_cls E) ≠
                                (nb095_alpha_dummy_810 u S_cls E) from (by
                                unfold nb095_alpha_dummy_810;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_814 D R S_cls E) from (by
          unfold nb095_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_817 u S_cls E) from (by
          unfold nb095_alpha_dummy_817;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_813 D R S_cls E) from (by
          unfold nb095_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_816 u S_cls E) from (by
          unfold nb095_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_811 D R S_cls E) from (by
          unfold nb095_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_812 u S_cls E) from (by
          unfold nb095_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_815 D R S_cls E), (nb095_alpha_dummy_818 u S_cls E)),
        ((nb095_alpha_dummy_814 D R S_cls E), (nb095_alpha_dummy_817 u S_cls E)),
        ((nb095_alpha_dummy_813 D R S_cls E), (nb095_alpha_dummy_816 u S_cls E)),
        ((nb095_alpha_dummy_811 D R S_cls E), (nb095_alpha_dummy_812 u S_cls E)),
        ((nb095_alpha_dummy_807 D R S_cls E), (nb095_alpha_dummy_809 u S_cls E)),
        ((nb095_alpha_dummy_808 D R S_cls E), (nb095_alpha_dummy_810 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_805 D R S_cls E), (nb095_alpha_dummy_806 u S_cls E)),
        ((nb095_alpha_dummy_803 D R S_cls E), (nb095_alpha_dummy_804 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814
        D R S_cls E) ≠ (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_815 D R S_cls E), (nb095_alpha_dummy_818 u S_cls E)),
        ((nb095_alpha_dummy_814 D R S_cls E), (nb095_alpha_dummy_817 u S_cls E)),
        ((nb095_alpha_dummy_813 D R S_cls E), (nb095_alpha_dummy_816 u S_cls E)),
        ((nb095_alpha_dummy_811 D R S_cls E), (nb095_alpha_dummy_812 u S_cls E)),
        ((nb095_alpha_dummy_807 D R S_cls E), (nb095_alpha_dummy_809 u S_cls E)),
        ((nb095_alpha_dummy_808 D R S_cls E), (nb095_alpha_dummy_810 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_805 D R S_cls E), (nb095_alpha_dummy_806 u S_cls E)),
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
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814
        D R S_cls E) ≠ (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_827
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815
        D R S_cls E) ≠ (nb095_alpha_dummy_827 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls
                    E)
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
                                    ((nb095_alpha_dummy_800 D R S_cls E),
                                      (nb095_alpha_dummy_802 u S_cls E)),
                                    ((nb095_alpha_dummy_799 D R S_cls E),
                                      (nb095_alpha_dummy_801 u S_cls E)),
                                    ((nb095_alpha_dummy_805 D R S_cls E),
                                      (nb095_alpha_dummy_806 u S_cls E)),
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
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0855 u S_cls E) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
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
                                    ((nb095_alpha_dummy_800 D R S_cls E),
                                      (nb095_alpha_dummy_802 u S_cls E)),
                                    ((nb095_alpha_dummy_799 D R S_cls E),
                                      (nb095_alpha_dummy_801 u S_cls E)),
                                    ((nb095_alpha_dummy_805 D R S_cls E),
                                      (nb095_alpha_dummy_806 u S_cls E)),
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
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                        (nb095_alpha_dummy_800 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_800;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from
                      (by
                        unfold nb095_alpha_dummy_802;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                          (nb095_alpha_dummy_799 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_799;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_795 u S_cls E) ≠
                          (nb095_alpha_dummy_801 u S_cls E) from (by
                          unfold nb095_alpha_dummy_801;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_793 D R S_cls E) ≠
                            (nb095_alpha_dummy_805 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_805;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0850 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_795 u S_cls E) ≠
                            (nb095_alpha_dummy_806 u S_cls E) from (by
                            unfold nb095_alpha_dummy_806;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0851 u S_cls E)
                                    0)))) (TAlphaVar.there (show
                            (nb095_alpha_dummy_793 D R S_cls E) ≠
                              (nb095_alpha_dummy_803 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_803;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0847 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_795 u S_cls E) ≠
                              (nb095_alpha_dummy_804 u S_cls E) from (by
                              unfold nb095_alpha_dummy_804;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0849 u S_cls E)
                                      0)))) (TAlphaVar.there (freshVar_injective (((syn_cin E
                                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn
                                        (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪
                                ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                      (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E)))))).fv) (by decide)) (freshVar_injective
                              (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                      (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
                                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                                      (syn_csn (Class.cv u))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_800 D R S_cls E) ≠
                                (nb095_alpha_dummy_807 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_807;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_802 u S_cls E) ≠
                                (nb095_alpha_dummy_809 u S_cls E) from (by
                                unfold nb095_alpha_dummy_809;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                        0)))) (TAlphaVar.there (show
                                (nb095_alpha_dummy_800 D R S_cls E) ≠
                                  (nb095_alpha_dummy_808 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_808;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_802 u S_cls E) ≠
                                  (nb095_alpha_dummy_810 u S_cls E) from (by
                                  unfold nb095_alpha_dummy_810;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0853 u S_cls E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_807 D R S_cls E) ≠ (nb095_alpha_dummy_814 D R S_cls E) from (by
          unfold nb095_alpha_dummy_814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_817 u S_cls E) from (by
          unfold nb095_alpha_dummy_817;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls
                    E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_813 D R S_cls E) from (by
          unfold nb095_alpha_dummy_813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_816 u S_cls E) from (by
          unfold nb095_alpha_dummy_816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_811 D R S_cls E) from (by
          unfold nb095_alpha_dummy_811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_809 u S_cls E) ≠
        (nb095_alpha_dummy_812 u S_cls E) from (by
          unfold nb095_alpha_dummy_812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_815 D R S_cls E), (nb095_alpha_dummy_818 u S_cls E)),
        ((nb095_alpha_dummy_814 D R S_cls E), (nb095_alpha_dummy_817 u S_cls E)),
        ((nb095_alpha_dummy_813 D R S_cls E), (nb095_alpha_dummy_816 u S_cls E)),
        ((nb095_alpha_dummy_811 D R S_cls E), (nb095_alpha_dummy_812 u S_cls E)),
        ((nb095_alpha_dummy_807 D R S_cls E), (nb095_alpha_dummy_809 u S_cls E)),
        ((nb095_alpha_dummy_808 D R S_cls E), (nb095_alpha_dummy_810 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_805 D R S_cls E), (nb095_alpha_dummy_806 u S_cls E)),
        ((nb095_alpha_dummy_803 D R S_cls E), (nb095_alpha_dummy_804 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814
        D R S_cls E) ≠ (nb095_alpha_dummy_821 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_821
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_821
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠ (nb095_alpha_dummy_821
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_822
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_819 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_820
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_815 D R S_cls E), (nb095_alpha_dummy_818 u S_cls E)),
        ((nb095_alpha_dummy_814 D R S_cls E), (nb095_alpha_dummy_817 u S_cls E)),
        ((nb095_alpha_dummy_813 D R S_cls E), (nb095_alpha_dummy_816 u S_cls E)),
        ((nb095_alpha_dummy_811 D R S_cls E), (nb095_alpha_dummy_812 u S_cls E)),
        ((nb095_alpha_dummy_807 D R S_cls E), (nb095_alpha_dummy_809 u S_cls E)),
        ((nb095_alpha_dummy_808 D R S_cls E), (nb095_alpha_dummy_810 u S_cls E)),
        ((nb095_alpha_dummy_800 D R S_cls E), (nb095_alpha_dummy_802 u S_cls E)),
        ((nb095_alpha_dummy_799 D R S_cls E), (nb095_alpha_dummy_801 u S_cls E)),
        ((nb095_alpha_dummy_805 D R S_cls E), (nb095_alpha_dummy_806 u S_cls E)),
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
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_814
        D R S_cls E) ≠ (nb095_alpha_dummy_825 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠ (nb095_alpha_dummy_825
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_826
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_814 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_817 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_807
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815
        D R S_cls E) ≠ (nb095_alpha_dummy_827 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_815
        D R S_cls E) ≠ (nb095_alpha_dummy_827 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_828
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_815 D R S_cls E) ≠
        (nb095_alpha_dummy_823 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_818 u S_cls E) ≠ (nb095_alpha_dummy_824
        u S_cls E) from (by
          unfold
            nb095_alpha_dummy_824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_811 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_811;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0854 D R S_cls E)
                                                  0)))) (show
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
                                      ((nb095_alpha_dummy_800 D R S_cls E),
                                        (nb095_alpha_dummy_802 u S_cls E)),
                                      ((nb095_alpha_dummy_799 D R S_cls E),
                                        (nb095_alpha_dummy_801 u S_cls E)),
                                      ((nb095_alpha_dummy_805 D R S_cls E),
                                        (nb095_alpha_dummy_806 u S_cls E)),
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
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0855 u S_cls E) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_807 D R S_cls E) ≠
        (nb095_alpha_dummy_811 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_811;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0854 D R S_cls E)
                                                  0)))) (show
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
                                      ((nb095_alpha_dummy_800 D R S_cls E),
                                        (nb095_alpha_dummy_802 u S_cls E)),
                                      ((nb095_alpha_dummy_799 D R S_cls E),
                                        (nb095_alpha_dummy_801 u S_cls E)),
                                      ((nb095_alpha_dummy_805 D R S_cls E),
                                        (nb095_alpha_dummy_806 u S_cls E)),
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
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
