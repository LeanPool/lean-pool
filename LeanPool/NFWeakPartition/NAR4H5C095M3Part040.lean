/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part039

/-! NF weak partition development: NAR4H5C095M3Part040. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0090`. -/
@[expose]
noncomputable def nb095SplitAlpha0090 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy683 D R S_cls E), (nb095AlphaDummy684 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy683 D R S_cls E))
          (Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy683 D R S_cls E))
            (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy684 x u D R S_cls f E))
          (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy684 x u D R S_cls f E))
            (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                  (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                      (nb095AlphaDummy678 D R S_cls E) from (by
                      unfold nb095AlphaDummy678;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1)))) (show
                    (nb095AlphaDummy005 x u D R S_cls f E) ≠
                      (nb095AlphaDummy680 x u D R S_cls f E) from (by
                      unfold nb095AlphaDummy680;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                        (nb095AlphaDummy677 D R S_cls E) from (by
                        unfold nb095AlphaDummy677;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                        (nb095AlphaDummy679 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy679;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095AlphaDummy003 D R S_cls E) ≠
                          (nb095AlphaDummy683 D R S_cls E) from (by
                          unfold nb095AlphaDummy683;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0706 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                          (nb095AlphaDummy684 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy684;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0707 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                            (nb095AlphaDummy681 D R S_cls E) from (by
                            unfold nb095AlphaDummy681;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0703 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                            (nb095AlphaDummy682 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy682;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0705 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                              (nb095AlphaDummy669 D R S_cls E) from (by
                              unfold nb095AlphaDummy669;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0696 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                              (nb095AlphaDummy670 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy670;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0699 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                (nb095AlphaDummy671 D R S_cls E) from (by
                                unfold nb095AlphaDummy671;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0697 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                (nb095AlphaDummy672 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy672;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0700 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                  (nb095AlphaDummy674 D R S_cls E) from (by
                                  unfold nb095AlphaDummy674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0698 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy676 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy676;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0701 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                    (nb095AlphaDummy673 D R S_cls E) from (by
                                    unfold nb095AlphaDummy673;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0698 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                    (nb095AlphaDummy675 x u D R S_cls f E) from (by
                                    unfold nb095AlphaDummy675;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0701 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy003 D R S_cls E) ≠
                                      (nb095AlphaDummy662 D R S_cls E) from (by
                                      unfold nb095AlphaDummy662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0690 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy664 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0692 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy003 D R S_cls E) ≠
                                        (nb095AlphaDummy661 D R S_cls E) from (by
                                        unfold nb095AlphaDummy661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0690 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy663 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0692 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy003 D R S_cls E) ≠
        (nb095AlphaDummy667 D R S_cls E) from (by
                                          unfold nb095AlphaDummy667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0694 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy005 x u D R S_cls f E) ≠
        (nb095AlphaDummy668 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0695 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0691 D R S_cls E)
                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
        (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0693 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D (synCima
        (synCcnv (synCdif R (synCid))) (synCsn (Class.cv (nb095AlphaDummy002 D
        R S_cls E))))) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
        (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E))))) (synCin E (synCima (synCcnv
        (synCdif S_cls (synCid))) (synCsn (Class.cv (nb095AlphaDummy001 D R
        S_cls E)))))))).fv ∪ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E (synCima
        (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E)))))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D (synCima (synCcnv
        (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D (synCima (synCcnv
        (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp
        (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
        (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn
        (Class.cv u))))))).fv ∪ ((synCin D (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv x))))).fv ∪ ((synCin E (synCima
        (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                              (nb095AlphaDummy685 D R S_cls E) from (by
                              unfold nb095AlphaDummy685;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                              (nb095AlphaDummy687 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy687;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0709 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                                (nb095AlphaDummy686 D R S_cls E) from (by
                                unfold nb095AlphaDummy686;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy680 x u D R S_cls f E) ≠
                                (nb095AlphaDummy688 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy688;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy692 D R S_cls E) from (by
          unfold nb095AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy695 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy691 D R S_cls E) from (by
          unfold nb095AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy694 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy689 D R S_cls E) from (by
          unfold nb095AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy693 D R S_cls E), (nb095AlphaDummy696 x u D R S_cls f E)),
        ((nb095AlphaDummy692 D R S_cls E), (nb095AlphaDummy695 x u D R S_cls f E)),
        ((nb095AlphaDummy691 D R S_cls E), (nb095AlphaDummy694 x u D R S_cls f E)),
        ((nb095AlphaDummy689 D R S_cls E), (nb095AlphaDummy690 x u D R S_cls f E)),
        ((nb095AlphaDummy685 D R S_cls E), (nb095AlphaDummy687 x u D R S_cls f E)),
        ((nb095AlphaDummy686 D R S_cls E), (nb095AlphaDummy688 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy683 D R S_cls E), (nb095AlphaDummy684 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692
        D R S_cls E) ≠ (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy693 D R S_cls E), (nb095AlphaDummy696 x u D R S_cls f E)),
        ((nb095AlphaDummy692 D R S_cls E), (nb095AlphaDummy695 x u D R S_cls f E)),
        ((nb095AlphaDummy691 D R S_cls E), (nb095AlphaDummy694 x u D R S_cls f E)),
        ((nb095AlphaDummy689 D R S_cls E), (nb095AlphaDummy690 x u D R S_cls f E)),
        ((nb095AlphaDummy685 D R S_cls E), (nb095AlphaDummy687 x u D R S_cls f E)),
        ((nb095AlphaDummy686 D R S_cls E), (nb095AlphaDummy688 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy683 D R S_cls E), (nb095AlphaDummy684 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692
        D R S_cls E) ≠ (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy704
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy704
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy706
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693
        D R S_cls E) ≠ (nb095AlphaDummy705 D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy706
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy685 D R S_cls E) ≠
                                        (nb095AlphaDummy689 D R S_cls E) from (by
                                        unfold nb095AlphaDummy689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy689 D R S_cls E),
                                      (nb095AlphaDummy690 x u D R S_cls f E)),
                                    ((nb095AlphaDummy685 D R S_cls E),
                                      (nb095AlphaDummy687 x u D R S_cls f E)),
                                    ((nb095AlphaDummy686 D R S_cls E),
                                      (nb095AlphaDummy688 x u D R S_cls f E)),
                                    ((nb095AlphaDummy678 D R S_cls E),
                                      (nb095AlphaDummy680 x u D R S_cls f E)),
                                    ((nb095AlphaDummy677 D R S_cls E),
                                      (nb095AlphaDummy679 x u D R S_cls f E)),
                                    ((nb095AlphaDummy683 D R S_cls E),
                                      (nb095AlphaDummy684 x u D R S_cls f E)),
                                    ((nb095AlphaDummy681 D R S_cls E),
                                      (nb095AlphaDummy682 x u D R S_cls f E)),
                                    ((nb095AlphaDummy669 D R S_cls E),
                                      (nb095AlphaDummy670 x u D R S_cls f E)),
                                    ((nb095AlphaDummy671 D R S_cls E),
                                      (nb095AlphaDummy672 x u D R S_cls f E)),
                                    ((nb095AlphaDummy674 D R S_cls E),
                                      (nb095AlphaDummy676 x u D R S_cls f E)),
                                    ((nb095AlphaDummy673 D R S_cls E),
                                      (nb095AlphaDummy675 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy667 D R S_cls E),
                                      (nb095AlphaDummy668 x u D R S_cls f E)),
                                    ((nb095AlphaDummy665 D R S_cls E),
                                      (nb095AlphaDummy666 x u D R S_cls f E)),
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
                                    (nb095AlphaDummy685 D R S_cls E) ≠
                                      (nb095AlphaDummy689 D R S_cls E) from (by
                                      unfold nb095AlphaDummy689;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy690;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0711 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy685 D R S_cls E) ≠
                                        (nb095AlphaDummy689 D R S_cls E) from (by
                                        unfold nb095AlphaDummy689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy689 D R S_cls E),
                                      (nb095AlphaDummy690 x u D R S_cls f E)),
                                    ((nb095AlphaDummy685 D R S_cls E),
                                      (nb095AlphaDummy687 x u D R S_cls f E)),
                                    ((nb095AlphaDummy686 D R S_cls E),
                                      (nb095AlphaDummy688 x u D R S_cls f E)),
                                    ((nb095AlphaDummy678 D R S_cls E),
                                      (nb095AlphaDummy680 x u D R S_cls f E)),
                                    ((nb095AlphaDummy677 D R S_cls E),
                                      (nb095AlphaDummy679 x u D R S_cls f E)),
                                    ((nb095AlphaDummy683 D R S_cls E),
                                      (nb095AlphaDummy684 x u D R S_cls f E)),
                                    ((nb095AlphaDummy681 D R S_cls E),
                                      (nb095AlphaDummy682 x u D R S_cls f E)),
                                    ((nb095AlphaDummy669 D R S_cls E),
                                      (nb095AlphaDummy670 x u D R S_cls f E)),
                                    ((nb095AlphaDummy671 D R S_cls E),
                                      (nb095AlphaDummy672 x u D R S_cls f E)),
                                    ((nb095AlphaDummy674 D R S_cls E),
                                      (nb095AlphaDummy676 x u D R S_cls f E)),
                                    ((nb095AlphaDummy673 D R S_cls E),
                                      (nb095AlphaDummy675 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy667 D R S_cls E),
                                      (nb095AlphaDummy668 x u D R S_cls f E)),
                                    ((nb095AlphaDummy665 D R S_cls E),
                                      (nb095AlphaDummy666 x u D R S_cls f E)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                        (nb095AlphaDummy678 D R S_cls E) from (by
                        unfold nb095AlphaDummy678;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                        (nb095AlphaDummy680 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy680;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095AlphaDummy003 D R S_cls E) ≠
                          (nb095AlphaDummy677 D R S_cls E) from (by
                          unfold nb095AlphaDummy677;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                          (nb095AlphaDummy679 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy679;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0704 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                            (nb095AlphaDummy683 D R S_cls E) from (by
                            unfold nb095AlphaDummy683;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0706 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                            (nb095AlphaDummy684 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy684;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0707 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                              (nb095AlphaDummy681 D R S_cls E) from (by
                              unfold nb095AlphaDummy681;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0703 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
                              (nb095AlphaDummy682 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy682;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0705 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                (nb095AlphaDummy669 D R S_cls E) from (by
                                unfold nb095AlphaDummy669;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0696 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                (nb095AlphaDummy670 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy670;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0699 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                  (nb095AlphaDummy671 D R S_cls E) from (by
                                  unfold nb095AlphaDummy671;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0697 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy672 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy672;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0700 x u D R S_cls f E) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
                                    (nb095AlphaDummy674 D R S_cls E) from (by
                                    unfold nb095AlphaDummy674;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0698 D R S_cls E) 1)))) (show
                                  (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                    (nb095AlphaDummy676 x u D R S_cls f E) from (by
                                    unfold nb095AlphaDummy676;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0701 x u D R S_cls f E)
                                            1)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy003 D R S_cls E) ≠
                                      (nb095AlphaDummy673 D R S_cls E) from (by
                                      unfold nb095AlphaDummy673;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0698 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy675 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy675;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0701 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy003 D R S_cls E) ≠
                                        (nb095AlphaDummy662 D R S_cls E) from (by
                                        unfold nb095AlphaDummy662;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0690 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy005 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy664 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy664;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0692 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy003 D R S_cls E) ≠
        (nb095AlphaDummy661 D R S_cls E) from (by
                                          unfold nb095AlphaDummy661;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0690 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy005 x u D R S_cls f E) ≠
        (nb095AlphaDummy663 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy663;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0692 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy667 D R S_cls E) from (by
          unfold nb095AlphaDummy667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0694 D R S_cls E)
                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
        (nb095AlphaDummy668 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0695 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy003 D R S_cls E) ≠
        (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0691 D R S_cls E)
                  0)))) (show (nb095AlphaDummy005 x u D R S_cls f E) ≠
        (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0693 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D (synCima
        (synCcnv (synCdif R (synCid))) (synCsn (Class.cv (nb095AlphaDummy002
        D R S_cls E))))) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪ ((synCin S_cls (synCxp
        (synCin E (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy001 D R S_cls E))))) (synCin E (synCima (synCcnv (synCdif S_cls
        (synCid))) (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
        (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E (synCima (synCcnv
        (synCdif S_cls (synCid))) (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls
        E)))))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((synCin R (synCxp
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv ∪
        ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv u)))) (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
        (synCsn (Class.cv u))))))).fv ∪ ((synCin D (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv x))))).fv ∪ ((synCin E (synCima (synCcnv
        (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy678 D R S_cls E) ≠
                                (nb095AlphaDummy685 D R S_cls E) from (by
                                unfold nb095AlphaDummy685;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy680 x u D R S_cls f E) ≠
                                (nb095AlphaDummy687 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy687;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0709 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                                  (nb095AlphaDummy686 D R S_cls E) from (by
                                  unfold nb095AlphaDummy686;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy680 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy688 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy688;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy685 D R S_cls E) ≠ (nb095AlphaDummy692 D R S_cls E) from (by
          unfold nb095AlphaDummy692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy695 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy691 D R S_cls E) from (by
          unfold nb095AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy694 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy689 D R S_cls E) from (by
          unfold nb095AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy693 D R S_cls E), (nb095AlphaDummy696 x u D R S_cls f E)),
        ((nb095AlphaDummy692 D R S_cls E), (nb095AlphaDummy695 x u D R S_cls f E)),
        ((nb095AlphaDummy691 D R S_cls E), (nb095AlphaDummy694 x u D R S_cls f E)),
        ((nb095AlphaDummy689 D R S_cls E), (nb095AlphaDummy690 x u D R S_cls f E)),
        ((nb095AlphaDummy685 D R S_cls E), (nb095AlphaDummy687 x u D R S_cls f E)),
        ((nb095AlphaDummy686 D R S_cls E), (nb095AlphaDummy688 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy683 D R S_cls E), (nb095AlphaDummy684 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692
        D R S_cls E) ≠ (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy700
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy698
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy693 D R S_cls E), (nb095AlphaDummy696 x u D R S_cls f E)),
        ((nb095AlphaDummy692 D R S_cls E), (nb095AlphaDummy695 x u D R S_cls f E)),
        ((nb095AlphaDummy691 D R S_cls E), (nb095AlphaDummy694 x u D R S_cls f E)),
        ((nb095AlphaDummy689 D R S_cls E), (nb095AlphaDummy690 x u D R S_cls f E)),
        ((nb095AlphaDummy685 D R S_cls E), (nb095AlphaDummy687 x u D R S_cls f E)),
        ((nb095AlphaDummy686 D R S_cls E), (nb095AlphaDummy688 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy683 D R S_cls E), (nb095AlphaDummy684 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692
        D R S_cls E) ≠ (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy704
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy704
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy706
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693
        D R S_cls E) ≠ (nb095AlphaDummy705 D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy706
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠ (nb095AlphaDummy702
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy689 D R S_cls E) from (by
                                          unfold nb095AlphaDummy689;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0710 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy690;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0711 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy689 D R S_cls E),
                                        (nb095AlphaDummy690 x u D R S_cls f E)),
                                      ((nb095AlphaDummy685 D R S_cls E),
                                        (nb095AlphaDummy687 x u D R S_cls f E)),
                                      ((nb095AlphaDummy686 D R S_cls E),
                                        (nb095AlphaDummy688 x u D R S_cls f E)),
                                      ((nb095AlphaDummy678 D R S_cls E),
                                        (nb095AlphaDummy680 x u D R S_cls f E)),
                                      ((nb095AlphaDummy677 D R S_cls E),
                                        (nb095AlphaDummy679 x u D R S_cls f E)),
                                      ((nb095AlphaDummy683 D R S_cls E),
                                        (nb095AlphaDummy684 x u D R S_cls f E)),
                                      ((nb095AlphaDummy681 D R S_cls E),
                                        (nb095AlphaDummy682 x u D R S_cls f E)),
                                      ((nb095AlphaDummy669 D R S_cls E),
                                        (nb095AlphaDummy670 x u D R S_cls f E)),
                                      ((nb095AlphaDummy671 D R S_cls E),
                                        (nb095AlphaDummy672 x u D R S_cls f E)),
                                      ((nb095AlphaDummy674 D R S_cls E),
                                        (nb095AlphaDummy676 x u D R S_cls f E)),
                                      ((nb095AlphaDummy673 D R S_cls E),
                                        (nb095AlphaDummy675 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy667 D R S_cls E),
                                        (nb095AlphaDummy668 x u D R S_cls f E)),
                                      ((nb095AlphaDummy665 D R S_cls E),
                                        (nb095AlphaDummy666 x u D R S_cls f E)),
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
                                      (nb095AlphaDummy685 D R S_cls E) ≠
                                        (nb095AlphaDummy689 D R S_cls E) from (by
                                        unfold nb095AlphaDummy689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy689 D R S_cls E) from (by
                                          unfold nb095AlphaDummy689;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0710 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy690;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0711 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy689 D R S_cls E),
                                        (nb095AlphaDummy690 x u D R S_cls f E)),
                                      ((nb095AlphaDummy685 D R S_cls E),
                                        (nb095AlphaDummy687 x u D R S_cls f E)),
                                      ((nb095AlphaDummy686 D R S_cls E),
                                        (nb095AlphaDummy688 x u D R S_cls f E)),
                                      ((nb095AlphaDummy678 D R S_cls E),
                                        (nb095AlphaDummy680 x u D R S_cls f E)),
                                      ((nb095AlphaDummy677 D R S_cls E),
                                        (nb095AlphaDummy679 x u D R S_cls f E)),
                                      ((nb095AlphaDummy683 D R S_cls E),
                                        (nb095AlphaDummy684 x u D R S_cls f E)),
                                      ((nb095AlphaDummy681 D R S_cls E),
                                        (nb095AlphaDummy682 x u D R S_cls f E)),
                                      ((nb095AlphaDummy669 D R S_cls E),
                                        (nb095AlphaDummy670 x u D R S_cls f E)),
                                      ((nb095AlphaDummy671 D R S_cls E),
                                        (nb095AlphaDummy672 x u D R S_cls f E)),
                                      ((nb095AlphaDummy674 D R S_cls E),
                                        (nb095AlphaDummy676 x u D R S_cls f E)),
                                      ((nb095AlphaDummy673 D R S_cls E),
                                        (nb095AlphaDummy675 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy667 D R S_cls E),
                                        (nb095AlphaDummy668 x u D R S_cls f E)),
                                      ((nb095AlphaDummy665 D R S_cls E),
                                        (nb095AlphaDummy666 x u D R S_cls f E)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0091`. -/
@[expose]
noncomputable def nb095SplitAlpha0091 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy711 D R S_cls E), (nb095AlphaDummy712 x u D R S_cls f E)),
        ((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy711 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy711 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy712 x u D R S_cls f E))
          (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy712 x u D R S_cls f E))
            (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                      (nb095AlphaDummy685 D R S_cls E) from (by
                      unfold nb095AlphaDummy685;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                    (nb095AlphaDummy680 x u D R S_cls f E) ≠
                      (nb095AlphaDummy687 x u D R S_cls f E) from (by
                      unfold nb095AlphaDummy687;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                              0)))) (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                        (nb095AlphaDummy686 D R S_cls E) from (by
                        unfold nb095AlphaDummy686;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy680 x u D R S_cls f E) ≠
                        (nb095AlphaDummy688 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy688;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095AlphaDummy678 D R S_cls E) ≠
                          (nb095AlphaDummy711 D R S_cls E) from (by
                          unfold nb095AlphaDummy711;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0738 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                          (nb095AlphaDummy712 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy712;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0739 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                            (nb095AlphaDummy709 D R S_cls E) from (by
                            unfold nb095AlphaDummy709;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0736 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                            (nb095AlphaDummy710 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy710;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0737 x u D R S_cls f E) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy685 D R S_cls E) ≠
                                        (nb095AlphaDummy692 D R S_cls E) from (by
                                        unfold nb095AlphaDummy692;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0712 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy695 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy695;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0713 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy691 D R S_cls E) from (by
                                          unfold nb095AlphaDummy691;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0712 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy694 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy694;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0713 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy685 D R S_cls E) ≠ (nb095AlphaDummy689 D R S_cls E) from (by
          unfold nb095AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy693 D R S_cls E),
        (nb095AlphaDummy696 x u D R S_cls f E)), ((nb095AlphaDummy692 D R S_cls E),
        (nb095AlphaDummy695 x u D R S_cls f E)), ((nb095AlphaDummy691 D R S_cls E),
        (nb095AlphaDummy694 x u D R S_cls f E)), ((nb095AlphaDummy689 D R S_cls E),
        (nb095AlphaDummy690 x u D R S_cls f E)), ((nb095AlphaDummy685 D R S_cls E),
        (nb095AlphaDummy687 x u D R S_cls f E)), ((nb095AlphaDummy686 D R S_cls E),
        (nb095AlphaDummy688 x u D R S_cls f E)), ((nb095AlphaDummy711 D R S_cls E),
        (nb095AlphaDummy712 x u D R S_cls f E)), ((nb095AlphaDummy709 D R S_cls E),
        (nb095AlphaDummy710 x u D R S_cls f E)), ((nb095AlphaDummy678 D R S_cls E),
        (nb095AlphaDummy680 x u D R S_cls f E)), ((nb095AlphaDummy677 D R S_cls E),
        (nb095AlphaDummy679 x u D R S_cls f E)), ((nb095AlphaDummy707 D R S_cls E),
        (nb095AlphaDummy708 x u D R S_cls f E)), ((nb095AlphaDummy681 D R S_cls E),
        (nb095AlphaDummy682 x u D R S_cls f E)), ((nb095AlphaDummy669 D R S_cls E),
        (nb095AlphaDummy670 x u D R S_cls f E)), ((nb095AlphaDummy671 D R S_cls E),
        (nb095AlphaDummy672 x u D R S_cls f E)), ((nb095AlphaDummy674 D R S_cls E),
        (nb095AlphaDummy676 x u D R S_cls f E)), ((nb095AlphaDummy673 D R S_cls E),
        (nb095AlphaDummy675 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy667 D R S_cls E),
        (nb095AlphaDummy668 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
        (nb095AlphaDummy666 x u D R S_cls f E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy693 D R S_cls E),
        (nb095AlphaDummy696 x u D R S_cls f E)), ((nb095AlphaDummy692 D R S_cls E),
        (nb095AlphaDummy695 x u D R S_cls f E)), ((nb095AlphaDummy691 D R S_cls E),
        (nb095AlphaDummy694 x u D R S_cls f E)), ((nb095AlphaDummy689 D R S_cls E),
        (nb095AlphaDummy690 x u D R S_cls f E)), ((nb095AlphaDummy685 D R S_cls E),
        (nb095AlphaDummy687 x u D R S_cls f E)), ((nb095AlphaDummy686 D R S_cls E),
        (nb095AlphaDummy688 x u D R S_cls f E)), ((nb095AlphaDummy711 D R S_cls E),
        (nb095AlphaDummy712 x u D R S_cls f E)), ((nb095AlphaDummy709 D R S_cls E),
        (nb095AlphaDummy710 x u D R S_cls f E)), ((nb095AlphaDummy678 D R S_cls E),
        (nb095AlphaDummy680 x u D R S_cls f E)), ((nb095AlphaDummy677 D R S_cls E),
        (nb095AlphaDummy679 x u D R S_cls f E)), ((nb095AlphaDummy707 D R S_cls E),
        (nb095AlphaDummy708 x u D R S_cls f E)), ((nb095AlphaDummy681 D R S_cls E),
        (nb095AlphaDummy682 x u D R S_cls f E)), ((nb095AlphaDummy669 D R S_cls E),
        (nb095AlphaDummy670 x u D R S_cls f E)), ((nb095AlphaDummy671 D R S_cls E),
        (nb095AlphaDummy672 x u D R S_cls f E)), ((nb095AlphaDummy674 D R S_cls E),
        (nb095AlphaDummy676 x u D R S_cls f E)), ((nb095AlphaDummy673 D R S_cls E),
        (nb095AlphaDummy675 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy667 D R S_cls E),
        (nb095AlphaDummy668 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
        (nb095AlphaDummy666 x u D R S_cls f E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy685 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy704 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy704 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy706 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705 D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy706 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy685 D R S_cls E) ≠
                                (nb095AlphaDummy689 D R S_cls E) from (by
                                unfold nb095AlphaDummy689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy689 D R S_cls E),
                              (nb095AlphaDummy690 x u D R S_cls f E)),
                            ((nb095AlphaDummy685 D R S_cls E),
                              (nb095AlphaDummy687 x u D R S_cls f E)),
                            ((nb095AlphaDummy686 D R S_cls E),
                              (nb095AlphaDummy688 x u D R S_cls f E)),
                            ((nb095AlphaDummy711 D R S_cls E),
                              (nb095AlphaDummy712 x u D R S_cls f E)),
                            ((nb095AlphaDummy709 D R S_cls E),
                              (nb095AlphaDummy710 x u D R S_cls f E)),
                            ((nb095AlphaDummy678 D R S_cls E),
                              (nb095AlphaDummy680 x u D R S_cls f E)),
                            ((nb095AlphaDummy677 D R S_cls E),
                              (nb095AlphaDummy679 x u D R S_cls f E)),
                            ((nb095AlphaDummy707 D R S_cls E),
                              (nb095AlphaDummy708 x u D R S_cls f E)),
                            ((nb095AlphaDummy681 D R S_cls E),
                              (nb095AlphaDummy682 x u D R S_cls f E)),
                            ((nb095AlphaDummy669 D R S_cls E),
                              (nb095AlphaDummy670 x u D R S_cls f E)),
                            ((nb095AlphaDummy671 D R S_cls E),
                              (nb095AlphaDummy672 x u D R S_cls f E)),
                            ((nb095AlphaDummy674 D R S_cls E),
                              (nb095AlphaDummy676 x u D R S_cls f E)),
                            ((nb095AlphaDummy673 D R S_cls E),
                              (nb095AlphaDummy675 x u D R S_cls f E)),
                            ((nb095AlphaDummy662 D R S_cls E),
                              (nb095AlphaDummy664 x u D R S_cls f E)),
                            ((nb095AlphaDummy661 D R S_cls E),
                              (nb095AlphaDummy663 x u D R S_cls f E)),
                            ((nb095AlphaDummy667 D R S_cls E),
                              (nb095AlphaDummy668 x u D R S_cls f E)),
                            ((nb095AlphaDummy665 D R S_cls E),
                              (nb095AlphaDummy666 x u D R S_cls f E)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
                              (nb095AlphaDummy689 D R S_cls E) from (by
                              unfold nb095AlphaDummy689;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0710 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
                              (nb095AlphaDummy690 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy690;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy685 D R S_cls E) ≠
                                (nb095AlphaDummy689 D R S_cls E) from (by
                                unfold nb095AlphaDummy689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy689 D R S_cls E),
                              (nb095AlphaDummy690 x u D R S_cls f E)),
                            ((nb095AlphaDummy685 D R S_cls E),
                              (nb095AlphaDummy687 x u D R S_cls f E)),
                            ((nb095AlphaDummy686 D R S_cls E),
                              (nb095AlphaDummy688 x u D R S_cls f E)),
                            ((nb095AlphaDummy711 D R S_cls E),
                              (nb095AlphaDummy712 x u D R S_cls f E)),
                            ((nb095AlphaDummy709 D R S_cls E),
                              (nb095AlphaDummy710 x u D R S_cls f E)),
                            ((nb095AlphaDummy678 D R S_cls E),
                              (nb095AlphaDummy680 x u D R S_cls f E)),
                            ((nb095AlphaDummy677 D R S_cls E),
                              (nb095AlphaDummy679 x u D R S_cls f E)),
                            ((nb095AlphaDummy707 D R S_cls E),
                              (nb095AlphaDummy708 x u D R S_cls f E)),
                            ((nb095AlphaDummy681 D R S_cls E),
                              (nb095AlphaDummy682 x u D R S_cls f E)),
                            ((nb095AlphaDummy669 D R S_cls E),
                              (nb095AlphaDummy670 x u D R S_cls f E)),
                            ((nb095AlphaDummy671 D R S_cls E),
                              (nb095AlphaDummy672 x u D R S_cls f E)),
                            ((nb095AlphaDummy674 D R S_cls E),
                              (nb095AlphaDummy676 x u D R S_cls f E)),
                            ((nb095AlphaDummy673 D R S_cls E),
                              (nb095AlphaDummy675 x u D R S_cls f E)),
                            ((nb095AlphaDummy662 D R S_cls E),
                              (nb095AlphaDummy664 x u D R S_cls f E)),
                            ((nb095AlphaDummy661 D R S_cls E),
                              (nb095AlphaDummy663 x u D R S_cls f E)),
                            ((nb095AlphaDummy667 D R S_cls E),
                              (nb095AlphaDummy668 x u D R S_cls f E)),
                            ((nb095AlphaDummy665 D R S_cls E),
                              (nb095AlphaDummy666 x u D R S_cls f E)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                        (nb095AlphaDummy685 D R S_cls E) from (by
                        unfold nb095AlphaDummy685;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy680 x u D R S_cls f E) ≠
                        (nb095AlphaDummy687 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy687;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095AlphaDummy678 D R S_cls E) ≠
                          (nb095AlphaDummy686 D R S_cls E) from (by
                          unfold nb095AlphaDummy686;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E)
                                  1)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                          (nb095AlphaDummy688 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy688;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                            (nb095AlphaDummy711 D R S_cls E) from (by
                            unfold nb095AlphaDummy711;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0738 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                            (nb095AlphaDummy712 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy712;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0739 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy678 D R S_cls E) ≠
                              (nb095AlphaDummy709 D R S_cls E) from (by
                              unfold nb095AlphaDummy709;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0736 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy680 x u D R S_cls f E) ≠
                              (nb095AlphaDummy710 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy710;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0737 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy678 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy680 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy692 D R S_cls E) from (by
                                          unfold nb095AlphaDummy692;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0712 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy695 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy695;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0713 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy685 D R S_cls E) ≠ (nb095AlphaDummy691 D R S_cls E) from (by
          unfold nb095AlphaDummy691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy694 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy685 D R S_cls E) ≠
        (nb095AlphaDummy689 D R S_cls E) from (by
          unfold nb095AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R S_cls E)
                  0)))) (show (nb095AlphaDummy687 x u D R S_cls f E) ≠
        (nb095AlphaDummy690 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy693 D R S_cls E),
        (nb095AlphaDummy696 x u D R S_cls f E)), ((nb095AlphaDummy692 D R S_cls E),
        (nb095AlphaDummy695 x u D R S_cls f E)), ((nb095AlphaDummy691 D R S_cls E),
        (nb095AlphaDummy694 x u D R S_cls f E)), ((nb095AlphaDummy689 D R S_cls E),
        (nb095AlphaDummy690 x u D R S_cls f E)), ((nb095AlphaDummy685 D R S_cls E),
        (nb095AlphaDummy687 x u D R S_cls f E)), ((nb095AlphaDummy686 D R S_cls E),
        (nb095AlphaDummy688 x u D R S_cls f E)), ((nb095AlphaDummy711 D R S_cls E),
        (nb095AlphaDummy712 x u D R S_cls f E)), ((nb095AlphaDummy709 D R S_cls E),
        (nb095AlphaDummy710 x u D R S_cls f E)), ((nb095AlphaDummy678 D R S_cls E),
        (nb095AlphaDummy680 x u D R S_cls f E)), ((nb095AlphaDummy677 D R S_cls E),
        (nb095AlphaDummy679 x u D R S_cls f E)), ((nb095AlphaDummy707 D R S_cls E),
        (nb095AlphaDummy708 x u D R S_cls f E)), ((nb095AlphaDummy681 D R S_cls E),
        (nb095AlphaDummy682 x u D R S_cls f E)), ((nb095AlphaDummy669 D R S_cls E),
        (nb095AlphaDummy670 x u D R S_cls f E)), ((nb095AlphaDummy671 D R S_cls E),
        (nb095AlphaDummy672 x u D R S_cls f E)), ((nb095AlphaDummy674 D R S_cls E),
        (nb095AlphaDummy676 x u D R S_cls f E)), ((nb095AlphaDummy673 D R S_cls E),
        (nb095AlphaDummy675 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy667 D R S_cls E),
        (nb095AlphaDummy668 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
        (nb095AlphaDummy666 x u D R S_cls f E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy699 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy699 D R S_cls E) from (by
          unfold
            nb095AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy700 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy697 D R S_cls E) from (by
          unfold
            nb095AlphaDummy697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy698 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy693 D R S_cls E), (nb095AlphaDummy696 x u D R S_cls f E)),
        ((nb095AlphaDummy692 D R S_cls E), (nb095AlphaDummy695 x u D R S_cls f E)),
        ((nb095AlphaDummy691 D R S_cls E), (nb095AlphaDummy694 x u D R S_cls f E)),
        ((nb095AlphaDummy689 D R S_cls E), (nb095AlphaDummy690 x u D R S_cls f E)),
        ((nb095AlphaDummy685 D R S_cls E), (nb095AlphaDummy687 x u D R S_cls f E)),
        ((nb095AlphaDummy686 D R S_cls E), (nb095AlphaDummy688 x u D R S_cls f E)),
        ((nb095AlphaDummy711 D R S_cls E), (nb095AlphaDummy712 x u D R S_cls f E)),
        ((nb095AlphaDummy709 D R S_cls E), (nb095AlphaDummy710 x u D R S_cls f E)),
        ((nb095AlphaDummy678 D R S_cls E), (nb095AlphaDummy680 x u D R S_cls f E)),
        ((nb095AlphaDummy677 D R S_cls E), (nb095AlphaDummy679 x u D R S_cls f E)),
        ((nb095AlphaDummy707 D R S_cls E), (nb095AlphaDummy708 x u D R S_cls f E)),
        ((nb095AlphaDummy681 D R S_cls E), (nb095AlphaDummy682 x u D R S_cls f E)),
        ((nb095AlphaDummy669 D R S_cls E), (nb095AlphaDummy670 x u D R S_cls f E)),
        ((nb095AlphaDummy671 D R S_cls E), (nb095AlphaDummy672 x u D R S_cls f E)),
        ((nb095AlphaDummy674 D R S_cls E), (nb095AlphaDummy676 x u D R S_cls f E)),
        ((nb095AlphaDummy673 D R S_cls E), (nb095AlphaDummy675 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy667 D R S_cls E), (nb095AlphaDummy668 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy685 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy692 D R S_cls E) ≠ (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy704 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy703 D R S_cls E) from (by
          unfold
            nb095AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy704 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy692 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy695 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy685
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy687 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy706 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy693 D R S_cls E) ≠ (nb095AlphaDummy705 D R S_cls E) from (by
          unfold
            nb095AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy706 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy693 D R S_cls E) ≠
        (nb095AlphaDummy701 D R S_cls E) from (by
          unfold
            nb095AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy696 x u D R S_cls f E) ≠
        (nb095AlphaDummy702 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy685 D R S_cls E) ≠
                                  (nb095AlphaDummy689 D R S_cls E) from (by
                                  unfold nb095AlphaDummy689;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy690;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy689 D R S_cls E),
                                (nb095AlphaDummy690 x u D R S_cls f E)),
                              ((nb095AlphaDummy685 D R S_cls E),
                                (nb095AlphaDummy687 x u D R S_cls f E)),
                              ((nb095AlphaDummy686 D R S_cls E),
                                (nb095AlphaDummy688 x u D R S_cls f E)),
                              ((nb095AlphaDummy711 D R S_cls E),
                                (nb095AlphaDummy712 x u D R S_cls f E)),
                              ((nb095AlphaDummy709 D R S_cls E),
                                (nb095AlphaDummy710 x u D R S_cls f E)),
                              ((nb095AlphaDummy678 D R S_cls E),
                                (nb095AlphaDummy680 x u D R S_cls f E)),
                              ((nb095AlphaDummy677 D R S_cls E),
                                (nb095AlphaDummy679 x u D R S_cls f E)),
                              ((nb095AlphaDummy707 D R S_cls E),
                                (nb095AlphaDummy708 x u D R S_cls f E)),
                              ((nb095AlphaDummy681 D R S_cls E),
                                (nb095AlphaDummy682 x u D R S_cls f E)),
                              ((nb095AlphaDummy669 D R S_cls E),
                                (nb095AlphaDummy670 x u D R S_cls f E)),
                              ((nb095AlphaDummy671 D R S_cls E),
                                (nb095AlphaDummy672 x u D R S_cls f E)),
                              ((nb095AlphaDummy674 D R S_cls E),
                                (nb095AlphaDummy676 x u D R S_cls f E)),
                              ((nb095AlphaDummy673 D R S_cls E),
                                (nb095AlphaDummy675 x u D R S_cls f E)),
                              ((nb095AlphaDummy662 D R S_cls E),
                                (nb095AlphaDummy664 x u D R S_cls f E)),
                              ((nb095AlphaDummy661 D R S_cls E),
                                (nb095AlphaDummy663 x u D R S_cls f E)),
                              ((nb095AlphaDummy667 D R S_cls E),
                                (nb095AlphaDummy668 x u D R S_cls f E)),
                              ((nb095AlphaDummy665 D R S_cls E),
                                (nb095AlphaDummy666 x u D R S_cls f E)),
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
                              (nb095AlphaDummy685 D R S_cls E) ≠
                                (nb095AlphaDummy689 D R S_cls E) from (by
                                unfold nb095AlphaDummy689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy685 D R S_cls E) ≠
                                  (nb095AlphaDummy689 D R S_cls E) from (by
                                  unfold nb095AlphaDummy689;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy687 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy690 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy690;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy689 D R S_cls E),
                                (nb095AlphaDummy690 x u D R S_cls f E)),
                              ((nb095AlphaDummy685 D R S_cls E),
                                (nb095AlphaDummy687 x u D R S_cls f E)),
                              ((nb095AlphaDummy686 D R S_cls E),
                                (nb095AlphaDummy688 x u D R S_cls f E)),
                              ((nb095AlphaDummy711 D R S_cls E),
                                (nb095AlphaDummy712 x u D R S_cls f E)),
                              ((nb095AlphaDummy709 D R S_cls E),
                                (nb095AlphaDummy710 x u D R S_cls f E)),
                              ((nb095AlphaDummy678 D R S_cls E),
                                (nb095AlphaDummy680 x u D R S_cls f E)),
                              ((nb095AlphaDummy677 D R S_cls E),
                                (nb095AlphaDummy679 x u D R S_cls f E)),
                              ((nb095AlphaDummy707 D R S_cls E),
                                (nb095AlphaDummy708 x u D R S_cls f E)),
                              ((nb095AlphaDummy681 D R S_cls E),
                                (nb095AlphaDummy682 x u D R S_cls f E)),
                              ((nb095AlphaDummy669 D R S_cls E),
                                (nb095AlphaDummy670 x u D R S_cls f E)),
                              ((nb095AlphaDummy671 D R S_cls E),
                                (nb095AlphaDummy672 x u D R S_cls f E)),
                              ((nb095AlphaDummy674 D R S_cls E),
                                (nb095AlphaDummy676 x u D R S_cls f E)),
                              ((nb095AlphaDummy673 D R S_cls E),
                                (nb095AlphaDummy675 x u D R S_cls f E)),
                              ((nb095AlphaDummy662 D R S_cls E),
                                (nb095AlphaDummy664 x u D R S_cls f E)),
                              ((nb095AlphaDummy661 D R S_cls E),
                                (nb095AlphaDummy663 x u D R S_cls f E)),
                              ((nb095AlphaDummy667 D R S_cls E),
                                (nb095AlphaDummy668 x u D R S_cls f E)),
                              ((nb095AlphaDummy665 D R S_cls E),
                                (nb095AlphaDummy666 x u D R S_cls f E)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
