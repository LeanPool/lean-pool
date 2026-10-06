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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0096`. -/
@[expose]
noncomputable def nb095SplitAlpha0096 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy805 D R S_cls E), (nb095AlphaDummy806 u S_cls E)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy805 D R S_cls E))
          (Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy805 D R S_cls E))
            (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy806 u S_cls E))
          (Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy806 u S_cls E))
            (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy795 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                      (nb095AlphaDummy800 D R S_cls E) from (by
                      unfold nb095AlphaDummy800;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1)))) (show
                    (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from
                    (by
                      unfold nb095AlphaDummy802;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                        (nb095AlphaDummy799 D R S_cls E) from (by
                        unfold nb095AlphaDummy799;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy801 u S_cls E) from
                      (by
                        unfold nb095AlphaDummy801;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                          (nb095AlphaDummy805 D R S_cls E) from (by
                          unfold nb095AlphaDummy805;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0850 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy795 u S_cls E) ≠
                          (nb095AlphaDummy806 u S_cls E) from (by
                          unfold nb095AlphaDummy806;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0851 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                            (nb095AlphaDummy803 D R S_cls E) from (by
                            unfold nb095AlphaDummy803;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0847 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy795 u S_cls E) ≠
                            (nb095AlphaDummy804 u S_cls E) from (by
                            unfold nb095AlphaDummy804;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0849 u S_cls E)
                                    0)))) (TAlphaVar.there (freshVar_injective (((synCin E
                                  (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn
                                      (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪
                              ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                                    (synCsn (Class.cv
                                        (nb095AlphaDummy001 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((synCin E
                                  (synCima (synCcnv (synCdif S_cls (synCid)))
                                    (synCsn (Class.cv u))))).fv ∪ ((synCin E
                                  (synCima (synCcnv (synCdif S_cls (synCid)))
                                    (synCsn (Class.cv u))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy800 D R S_cls E) ≠
                              (nb095AlphaDummy807 D R S_cls E) from (by
                              unfold nb095AlphaDummy807;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0852 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy802 u S_cls E) ≠
                              (nb095AlphaDummy809 u S_cls E) from (by
                              unfold nb095AlphaDummy809;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                      0)))) (TAlphaVar.there (show
                              (nb095AlphaDummy800 D R S_cls E) ≠
                                (nb095AlphaDummy808 D R S_cls E) from (by
                                unfold nb095AlphaDummy808;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy802 u S_cls E) ≠
                                (nb095AlphaDummy810 u S_cls E) from (by
                                unfold nb095AlphaDummy810;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy814 D R S_cls E) from (by
          unfold nb095AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy817 u S_cls E) from (by
          unfold nb095AlphaDummy817;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy813 D R S_cls E) from (by
          unfold nb095AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy816 u S_cls E) from (by
          unfold nb095AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy811 D R S_cls E) from (by
          unfold nb095AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy812 u S_cls E) from (by
          unfold nb095AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy815 D R S_cls E), (nb095AlphaDummy818 u S_cls E)),
        ((nb095AlphaDummy814 D R S_cls E), (nb095AlphaDummy817 u S_cls E)),
        ((nb095AlphaDummy813 D R S_cls E), (nb095AlphaDummy816 u S_cls E)),
        ((nb095AlphaDummy811 D R S_cls E), (nb095AlphaDummy812 u S_cls E)),
        ((nb095AlphaDummy807 D R S_cls E), (nb095AlphaDummy809 u S_cls E)),
        ((nb095AlphaDummy808 D R S_cls E), (nb095AlphaDummy810 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy805 D R S_cls E), (nb095AlphaDummy806 u S_cls E)),
        ((nb095AlphaDummy803 D R S_cls E), (nb095AlphaDummy804 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814
        D R S_cls E) ≠ (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
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
        (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy815 D R S_cls E), (nb095AlphaDummy818 u S_cls E)),
        ((nb095AlphaDummy814 D R S_cls E), (nb095AlphaDummy817 u S_cls E)),
        ((nb095AlphaDummy813 D R S_cls E), (nb095AlphaDummy816 u S_cls E)),
        ((nb095AlphaDummy811 D R S_cls E), (nb095AlphaDummy812 u S_cls E)),
        ((nb095AlphaDummy807 D R S_cls E), (nb095AlphaDummy809 u S_cls E)),
        ((nb095AlphaDummy808 D R S_cls E), (nb095AlphaDummy810 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy805 D R S_cls E), (nb095AlphaDummy806 u S_cls E)),
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
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814
        D R S_cls E) ≠ (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls
                    E)
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
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy827
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815
        D R S_cls E) ≠ (nb095AlphaDummy827 D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828
        u S_cls E) from (by
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
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u S_cls
                    E)
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
                                    ((nb095AlphaDummy800 D R S_cls E),
                                      (nb095AlphaDummy802 u S_cls E)),
                                    ((nb095AlphaDummy799 D R S_cls E),
                                      (nb095AlphaDummy801 u S_cls E)),
                                    ((nb095AlphaDummy805 D R S_cls E),
                                      (nb095AlphaDummy806 u S_cls E)),
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
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0855 u S_cls E) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
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
                                    ((nb095AlphaDummy800 D R S_cls E),
                                      (nb095AlphaDummy802 u S_cls E)),
                                    ((nb095AlphaDummy799 D R S_cls E),
                                      (nb095AlphaDummy801 u S_cls E)),
                                    ((nb095AlphaDummy805 D R S_cls E),
                                      (nb095AlphaDummy806 u S_cls E)),
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
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                        (nb095AlphaDummy800 D R S_cls E) from (by
                        unfold nb095AlphaDummy800;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from
                      (by
                        unfold nb095AlphaDummy802;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                          (nb095AlphaDummy799 D R S_cls E) from (by
                          unfold nb095AlphaDummy799;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy795 u S_cls E) ≠
                          (nb095AlphaDummy801 u S_cls E) from (by
                          unfold nb095AlphaDummy801;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy793 D R S_cls E) ≠
                            (nb095AlphaDummy805 D R S_cls E) from (by
                            unfold nb095AlphaDummy805;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0850 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy795 u S_cls E) ≠
                            (nb095AlphaDummy806 u S_cls E) from (by
                            unfold nb095AlphaDummy806;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0851 u S_cls E)
                                    0)))) (TAlphaVar.there (show
                            (nb095AlphaDummy793 D R S_cls E) ≠
                              (nb095AlphaDummy803 D R S_cls E) from (by
                              unfold nb095AlphaDummy803;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0847 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy795 u S_cls E) ≠
                              (nb095AlphaDummy804 u S_cls E) from (by
                              unfold nb095AlphaDummy804;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0849 u S_cls E)
                                      0)))) (TAlphaVar.there (freshVar_injective (((synCin E
                                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn
                                        (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪
                                ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                                      (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E)))))).fv) (by decide)) (freshVar_injective
                              (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                                      (synCsn (Class.cv u))))).fv ∪ ((synCin E
                                    (synCima (synCcnv (synCdif S_cls (synCid)))
                                      (synCsn (Class.cv u))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy800 D R S_cls E) ≠
                                (nb095AlphaDummy807 D R S_cls E) from (by
                                unfold nb095AlphaDummy807;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0852 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy802 u S_cls E) ≠
                                (nb095AlphaDummy809 u S_cls E) from (by
                                unfold nb095AlphaDummy809;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0853 u S_cls E)
                                        0)))) (TAlphaVar.there (show
                                (nb095AlphaDummy800 D R S_cls E) ≠
                                  (nb095AlphaDummy808 D R S_cls E) from (by
                                  unfold nb095AlphaDummy808;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0852 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy802 u S_cls E) ≠
                                  (nb095AlphaDummy810 u S_cls E) from (by
                                  unfold nb095AlphaDummy810;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0853 u S_cls E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy807 D R S_cls E) ≠ (nb095AlphaDummy814 D R S_cls E) from (by
          unfold nb095AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy817 u S_cls E) from (by
          unfold nb095AlphaDummy817;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u S_cls
                    E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy813 D R S_cls E) from (by
          unfold nb095AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0856 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy816 u S_cls E) from (by
          unfold nb095AlphaDummy816;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0857 u
                    S_cls E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy811 D R S_cls E) from (by
          unfold nb095AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0854 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy809 u S_cls E) ≠
        (nb095AlphaDummy812 u S_cls E) from (by
          unfold nb095AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0855 u
                    S_cls E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy815 D R S_cls E), (nb095AlphaDummy818 u S_cls E)),
        ((nb095AlphaDummy814 D R S_cls E), (nb095AlphaDummy817 u S_cls E)),
        ((nb095AlphaDummy813 D R S_cls E), (nb095AlphaDummy816 u S_cls E)),
        ((nb095AlphaDummy811 D R S_cls E), (nb095AlphaDummy812 u S_cls E)),
        ((nb095AlphaDummy807 D R S_cls E), (nb095AlphaDummy809 u S_cls E)),
        ((nb095AlphaDummy808 D R S_cls E), (nb095AlphaDummy810 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy805 D R S_cls E), (nb095AlphaDummy806 u S_cls E)),
        ((nb095AlphaDummy803 D R S_cls E), (nb095AlphaDummy804 u S_cls E)),
        ((nb095AlphaDummy794 D R S_cls E), (nb095AlphaDummy796 u S_cls E)),
        ((nb095AlphaDummy793 D R S_cls E), (nb095AlphaDummy795 u S_cls E)),
        ((nb095AlphaDummy797 D R S_cls E), (nb095AlphaDummy798 u S_cls E)),
        ((nb095AlphaDummy791 D R S_cls E), (nb095AlphaDummy792 u S_cls E)),
        ((nb095AlphaDummy789 D R S_cls E), (nb095AlphaDummy790 u S_cls E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814
        D R S_cls E) ≠ (nb095AlphaDummy821 D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy821
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
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
        (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy821
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0860
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0861
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0858
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0859
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠ (nb095AlphaDummy821
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy821;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0864
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy822
        u S_cls E) from (by
          unfold
            nb095AlphaDummy822;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0865
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy819 D R S_cls E) from (by
          unfold
            nb095AlphaDummy819;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0862
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy820
        u S_cls E) from (by
          unfold
            nb095AlphaDummy820;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0863
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy815 D R S_cls E), (nb095AlphaDummy818 u S_cls E)),
        ((nb095AlphaDummy814 D R S_cls E), (nb095AlphaDummy817 u S_cls E)),
        ((nb095AlphaDummy813 D R S_cls E), (nb095AlphaDummy816 u S_cls E)),
        ((nb095AlphaDummy811 D R S_cls E), (nb095AlphaDummy812 u S_cls E)),
        ((nb095AlphaDummy807 D R S_cls E), (nb095AlphaDummy809 u S_cls E)),
        ((nb095AlphaDummy808 D R S_cls E), (nb095AlphaDummy810 u S_cls E)),
        ((nb095AlphaDummy800 D R S_cls E), (nb095AlphaDummy802 u S_cls E)),
        ((nb095AlphaDummy799 D R S_cls E), (nb095AlphaDummy801 u S_cls E)),
        ((nb095AlphaDummy805 D R S_cls E), (nb095AlphaDummy806 u S_cls E)),
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
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy814
        D R S_cls E) ≠ (nb095AlphaDummy825 D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826
        u S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠ (nb095AlphaDummy825
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy825;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0868
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy826
        u S_cls E) from (by
          unfold
            nb095AlphaDummy826;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0869
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy814 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0866
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy817 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0867
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy807
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815
        D R S_cls E) ≠ (nb095AlphaDummy827 D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828
        u S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0871
                    u
                    S_cls
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy815
        D R S_cls E) ≠ (nb095AlphaDummy827 D R S_cls E) from (by
          unfold
            nb095AlphaDummy827;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0872
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy828
        u S_cls E) from (by
          unfold
            nb095AlphaDummy828;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0873
                    u S_cls
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy815 D R S_cls E) ≠
        (nb095AlphaDummy823 D R S_cls E) from (by
          unfold
            nb095AlphaDummy823;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0870
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy818 u S_cls E) ≠ (nb095AlphaDummy824
        u S_cls E) from (by
          unfold
            nb095AlphaDummy824;
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
                                        (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy811 D R S_cls E) from (by
                                          unfold nb095AlphaDummy811;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0854 D R S_cls E)
                                                  0)))) (show
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
                                      ((nb095AlphaDummy800 D R S_cls E),
                                        (nb095AlphaDummy802 u S_cls E)),
                                      ((nb095AlphaDummy799 D R S_cls E),
                                        (nb095AlphaDummy801 u S_cls E)),
                                      ((nb095AlphaDummy805 D R S_cls E),
                                        (nb095AlphaDummy806 u S_cls E)),
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
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0855 u S_cls E) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy807 D R S_cls E) ≠
        (nb095AlphaDummy811 D R S_cls E) from (by
                                          unfold nb095AlphaDummy811;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0854 D R S_cls E)
                                                  0)))) (show
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
                                      ((nb095AlphaDummy800 D R S_cls E),
                                        (nb095AlphaDummy802 u S_cls E)),
                                      ((nb095AlphaDummy799 D R S_cls E),
                                        (nb095AlphaDummy801 u S_cls E)),
                                      ((nb095AlphaDummy805 D R S_cls E),
                                        (nb095AlphaDummy806 u S_cls E)),
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
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
