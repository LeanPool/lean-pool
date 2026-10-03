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

@[expose]
noncomputable def nb095_split_alpha_0090 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_683 D R S_cls E), (nb095_alpha_dummy_684 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_683 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_683 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_684 x u D R S_cls f E))
          (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_684 x u D R S_cls f E))
            (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                      (nb095_alpha_dummy_678 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_678;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1)))) (show
                    (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                      (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
                      unfold nb095_alpha_dummy_680;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                        (nb095_alpha_dummy_677 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_677;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_679;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_003 D R S_cls E) ≠
                          (nb095_alpha_dummy_683 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_683;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0706 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_684 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_684;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0707 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                            (nb095_alpha_dummy_681 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_681;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0703 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_682 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_682;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0705 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                              (nb095_alpha_dummy_669 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_669;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0696 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_670;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0699 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                (nb095_alpha_dummy_671 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_671;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0697 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_672 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_672;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0700 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                  (nb095_alpha_dummy_674 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0698 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_676 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_676;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0701 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                    (nb095_alpha_dummy_673 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_673;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0698 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                    (nb095_alpha_dummy_675 x u D R S_cls f E) from (by
                                    unfold nb095_alpha_dummy_675;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0701 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_003 D R S_cls E) ≠
                                      (nb095_alpha_dummy_662 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0690 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0692 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_003 D R S_cls E) ≠
                                        (nb095_alpha_dummy_661 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0690 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0692 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_003 D R S_cls E) ≠
        (nb095_alpha_dummy_667 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_667;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0694 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_668 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_668;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0695 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0691 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0693 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D (syn_cima
        (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv (nb095_alpha_dummy_002 D
        R S_cls E))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
        (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E (syn_cima (syn_ccnv
        (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv (nb095_alpha_dummy_001 D R
        S_cls E)))))))).fv ∪ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E (syn_cima
        (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E)))))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv
        (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D (syn_cima (syn_ccnv
        (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn
        (Class.cv u))))))).fv ∪ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv x))))).fv ∪ ((syn_cin E (syn_cima
        (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                              (nb095_alpha_dummy_685 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_685;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_687 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_687;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0709 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                                (nb095_alpha_dummy_686 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_686;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_688 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_688;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_692 D R S_cls E) from (by
          unfold nb095_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_695 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_691 D R S_cls E) from (by
          unfold nb095_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_694 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_689 D R S_cls E) from (by
          unfold nb095_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_693 D R S_cls E), (nb095_alpha_dummy_696 x u D R S_cls f E)),
        ((nb095_alpha_dummy_692 D R S_cls E), (nb095_alpha_dummy_695 x u D R S_cls f E)),
        ((nb095_alpha_dummy_691 D R S_cls E), (nb095_alpha_dummy_694 x u D R S_cls f E)),
        ((nb095_alpha_dummy_689 D R S_cls E), (nb095_alpha_dummy_690 x u D R S_cls f E)),
        ((nb095_alpha_dummy_685 D R S_cls E), (nb095_alpha_dummy_687 x u D R S_cls f E)),
        ((nb095_alpha_dummy_686 D R S_cls E), (nb095_alpha_dummy_688 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_683 D R S_cls E), (nb095_alpha_dummy_684 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692
        D R S_cls E) ≠ (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_693 D R S_cls E), (nb095_alpha_dummy_696 x u D R S_cls f E)),
        ((nb095_alpha_dummy_692 D R S_cls E), (nb095_alpha_dummy_695 x u D R S_cls f E)),
        ((nb095_alpha_dummy_691 D R S_cls E), (nb095_alpha_dummy_694 x u D R S_cls f E)),
        ((nb095_alpha_dummy_689 D R S_cls E), (nb095_alpha_dummy_690 x u D R S_cls f E)),
        ((nb095_alpha_dummy_685 D R S_cls E), (nb095_alpha_dummy_687 x u D R S_cls f E)),
        ((nb095_alpha_dummy_686 D R S_cls E), (nb095_alpha_dummy_688 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_683 D R S_cls E), (nb095_alpha_dummy_684 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692
        D R S_cls E) ≠ (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_704
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_704
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_706
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693
        D R S_cls E) ≠ (nb095_alpha_dummy_705 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_706
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
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
                                      (nb095_alpha_dummy_685 D R S_cls E) ≠
                                        (nb095_alpha_dummy_689 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_689 D R S_cls E),
                                      (nb095_alpha_dummy_690 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_685 D R S_cls E),
                                      (nb095_alpha_dummy_687 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_686 D R S_cls E),
                                      (nb095_alpha_dummy_688 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_678 D R S_cls E),
                                      (nb095_alpha_dummy_680 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_677 D R S_cls E),
                                      (nb095_alpha_dummy_679 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_683 D R S_cls E),
                                      (nb095_alpha_dummy_684 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_681 D R S_cls E),
                                      (nb095_alpha_dummy_682 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_669 D R S_cls E),
                                      (nb095_alpha_dummy_670 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_671 D R S_cls E),
                                      (nb095_alpha_dummy_672 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_674 D R S_cls E),
                                      (nb095_alpha_dummy_676 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_673 D R S_cls E),
                                      (nb095_alpha_dummy_675 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_667 D R S_cls E),
                                      (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_665 D R S_cls E),
                                      (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                                    (nb095_alpha_dummy_685 D R S_cls E) ≠
                                      (nb095_alpha_dummy_689 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_689;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_690;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0711 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_685 D R S_cls E) ≠
                                        (nb095_alpha_dummy_689 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_689 D R S_cls E),
                                      (nb095_alpha_dummy_690 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_685 D R S_cls E),
                                      (nb095_alpha_dummy_687 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_686 D R S_cls E),
                                      (nb095_alpha_dummy_688 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_678 D R S_cls E),
                                      (nb095_alpha_dummy_680 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_677 D R S_cls E),
                                      (nb095_alpha_dummy_679 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_683 D R S_cls E),
                                      (nb095_alpha_dummy_684 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_681 D R S_cls E),
                                      (nb095_alpha_dummy_682 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_669 D R S_cls E),
                                      (nb095_alpha_dummy_670 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_671 D R S_cls E),
                                      (nb095_alpha_dummy_672 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_674 D R S_cls E),
                                      (nb095_alpha_dummy_676 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_673 D R S_cls E),
                                      (nb095_alpha_dummy_675 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_667 D R S_cls E),
                                      (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_665 D R S_cls E),
                                      (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                        (nb095_alpha_dummy_678 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_678;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_680;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0704 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_003 D R S_cls E) ≠
                          (nb095_alpha_dummy_677 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_677;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0702 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_679;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0704 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                            (nb095_alpha_dummy_683 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_683;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0706 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_684 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_684;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0707 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                              (nb095_alpha_dummy_681 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_681;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0703 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_682 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_682;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0705 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                (nb095_alpha_dummy_669 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_669;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0696 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_670;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0699 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                  (nb095_alpha_dummy_671 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_671;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0697 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_672 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_672;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0700 x u D R S_cls f E) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
                                    (nb095_alpha_dummy_674 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_674;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0698 D R S_cls E) 1)))) (show
                                  (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                    (nb095_alpha_dummy_676 x u D R S_cls f E) from (by
                                    unfold nb095_alpha_dummy_676;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0701 x u D R S_cls f E)
                                            1)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_003 D R S_cls E) ≠
                                      (nb095_alpha_dummy_673 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_673;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0698 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_675 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_675;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0701 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_003 D R S_cls E) ≠
                                        (nb095_alpha_dummy_662 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_662;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0690 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_664;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0692 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_003 D R S_cls E) ≠
        (nb095_alpha_dummy_661 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_661;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0690 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_663;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0692 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_003 D R S_cls E) ≠ (nb095_alpha_dummy_667 D R S_cls E) from (by
          unfold nb095_alpha_dummy_667;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0694 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_668 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_668;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0695 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_003 D R S_cls E) ≠
        (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0691 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_005 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0693 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D (syn_cima
        (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv (nb095_alpha_dummy_002
        D R S_cls E))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪ ((syn_cin S_cls (syn_cxp
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls
        (syn_cid))) (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
        (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E (syn_cima (syn_ccnv
        (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls
        E)))))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv ∪
        ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv u)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv x))))).fv ∪ ((syn_cin E (syn_cima (syn_ccnv
        (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_678 D R S_cls E) ≠
                                (nb095_alpha_dummy_685 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_685;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_687 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_687;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0709 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                                  (nb095_alpha_dummy_686 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_686;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_688 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_688;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_685 D R S_cls E) ≠ (nb095_alpha_dummy_692 D R S_cls E) from (by
          unfold nb095_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_695 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_691 D R S_cls E) from (by
          unfold nb095_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_694 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_689 D R S_cls E) from (by
          unfold nb095_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_693 D R S_cls E), (nb095_alpha_dummy_696 x u D R S_cls f E)),
        ((nb095_alpha_dummy_692 D R S_cls E), (nb095_alpha_dummy_695 x u D R S_cls f E)),
        ((nb095_alpha_dummy_691 D R S_cls E), (nb095_alpha_dummy_694 x u D R S_cls f E)),
        ((nb095_alpha_dummy_689 D R S_cls E), (nb095_alpha_dummy_690 x u D R S_cls f E)),
        ((nb095_alpha_dummy_685 D R S_cls E), (nb095_alpha_dummy_687 x u D R S_cls f E)),
        ((nb095_alpha_dummy_686 D R S_cls E), (nb095_alpha_dummy_688 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_683 D R S_cls E), (nb095_alpha_dummy_684 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692
        D R S_cls E) ≠ (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_700
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_698
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_693 D R S_cls E), (nb095_alpha_dummy_696 x u D R S_cls f E)),
        ((nb095_alpha_dummy_692 D R S_cls E), (nb095_alpha_dummy_695 x u D R S_cls f E)),
        ((nb095_alpha_dummy_691 D R S_cls E), (nb095_alpha_dummy_694 x u D R S_cls f E)),
        ((nb095_alpha_dummy_689 D R S_cls E), (nb095_alpha_dummy_690 x u D R S_cls f E)),
        ((nb095_alpha_dummy_685 D R S_cls E), (nb095_alpha_dummy_687 x u D R S_cls f E)),
        ((nb095_alpha_dummy_686 D R S_cls E), (nb095_alpha_dummy_688 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_683 D R S_cls E), (nb095_alpha_dummy_684 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692
        D R S_cls E) ≠ (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_704
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_704
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_706
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693
        D R S_cls E) ≠ (nb095_alpha_dummy_705 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_706
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠ (nb095_alpha_dummy_702
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
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
                                        (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_689 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_689;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0710 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_690;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0711 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_689 D R S_cls E),
                                        (nb095_alpha_dummy_690 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_685 D R S_cls E),
                                        (nb095_alpha_dummy_687 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_686 D R S_cls E),
                                        (nb095_alpha_dummy_688 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_678 D R S_cls E),
                                        (nb095_alpha_dummy_680 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_677 D R S_cls E),
                                        (nb095_alpha_dummy_679 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_683 D R S_cls E),
                                        (nb095_alpha_dummy_684 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_681 D R S_cls E),
                                        (nb095_alpha_dummy_682 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_669 D R S_cls E),
                                        (nb095_alpha_dummy_670 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_671 D R S_cls E),
                                        (nb095_alpha_dummy_672 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_674 D R S_cls E),
                                        (nb095_alpha_dummy_676 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_673 D R S_cls E),
                                        (nb095_alpha_dummy_675 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_667 D R S_cls E),
                                        (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_665 D R S_cls E),
                                        (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                                      (nb095_alpha_dummy_685 D R S_cls E) ≠
                                        (nb095_alpha_dummy_689 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_689;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_690;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0711 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_689 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_689;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0710 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_690;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0711 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_689 D R S_cls E),
                                        (nb095_alpha_dummy_690 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_685 D R S_cls E),
                                        (nb095_alpha_dummy_687 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_686 D R S_cls E),
                                        (nb095_alpha_dummy_688 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_678 D R S_cls E),
                                        (nb095_alpha_dummy_680 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_677 D R S_cls E),
                                        (nb095_alpha_dummy_679 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_683 D R S_cls E),
                                        (nb095_alpha_dummy_684 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_681 D R S_cls E),
                                        (nb095_alpha_dummy_682 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_669 D R S_cls E),
                                        (nb095_alpha_dummy_670 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_671 D R S_cls E),
                                        (nb095_alpha_dummy_672 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_674 D R S_cls E),
                                        (nb095_alpha_dummy_676 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_673 D R S_cls E),
                                        (nb095_alpha_dummy_675 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_667 D R S_cls E),
                                        (nb095_alpha_dummy_668 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_665 D R S_cls E),
                                        (nb095_alpha_dummy_666 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_004 D R S_cls E),
                                        (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_003 D R S_cls E),
                                        (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0091 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_711 D R S_cls E), (nb095_alpha_dummy_712 x u D R S_cls f E)),
        ((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_711 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_711 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_712 x u D R S_cls f E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_712 x u D R S_cls f E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                      (nb095_alpha_dummy_685 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_685;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                    (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                      (nb095_alpha_dummy_687 x u D R S_cls f E) from (by
                      unfold nb095_alpha_dummy_687;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                              0)))) (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                        (nb095_alpha_dummy_686 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_686;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_688 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_688;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_678 D R S_cls E) ≠
                          (nb095_alpha_dummy_711 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_711;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0738 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_712 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_712;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0739 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                            (nb095_alpha_dummy_709 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_709;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0736 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_710 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_710;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0737 x u D R S_cls f E) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_685 D R S_cls E) ≠
                                        (nb095_alpha_dummy_692 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_692;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0712 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_695 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_695;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0713 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_691 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_691;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0712 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_694 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_694;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0713 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_685 D R S_cls E) ≠ (nb095_alpha_dummy_689 D R S_cls E) from (by
          unfold nb095_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_693 D R S_cls E),
        (nb095_alpha_dummy_696 x u D R S_cls f E)), ((nb095_alpha_dummy_692 D R S_cls E),
        (nb095_alpha_dummy_695 x u D R S_cls f E)), ((nb095_alpha_dummy_691 D R S_cls E),
        (nb095_alpha_dummy_694 x u D R S_cls f E)), ((nb095_alpha_dummy_689 D R S_cls E),
        (nb095_alpha_dummy_690 x u D R S_cls f E)), ((nb095_alpha_dummy_685 D R S_cls E),
        (nb095_alpha_dummy_687 x u D R S_cls f E)), ((nb095_alpha_dummy_686 D R S_cls E),
        (nb095_alpha_dummy_688 x u D R S_cls f E)), ((nb095_alpha_dummy_711 D R S_cls E),
        (nb095_alpha_dummy_712 x u D R S_cls f E)), ((nb095_alpha_dummy_709 D R S_cls E),
        (nb095_alpha_dummy_710 x u D R S_cls f E)), ((nb095_alpha_dummy_678 D R S_cls E),
        (nb095_alpha_dummy_680 x u D R S_cls f E)), ((nb095_alpha_dummy_677 D R S_cls E),
        (nb095_alpha_dummy_679 x u D R S_cls f E)), ((nb095_alpha_dummy_707 D R S_cls E),
        (nb095_alpha_dummy_708 x u D R S_cls f E)), ((nb095_alpha_dummy_681 D R S_cls E),
        (nb095_alpha_dummy_682 x u D R S_cls f E)), ((nb095_alpha_dummy_669 D R S_cls E),
        (nb095_alpha_dummy_670 x u D R S_cls f E)), ((nb095_alpha_dummy_671 D R S_cls E),
        (nb095_alpha_dummy_672 x u D R S_cls f E)), ((nb095_alpha_dummy_674 D R S_cls E),
        (nb095_alpha_dummy_676 x u D R S_cls f E)), ((nb095_alpha_dummy_673 D R S_cls E),
        (nb095_alpha_dummy_675 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_667 D R S_cls E),
        (nb095_alpha_dummy_668 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
        (nb095_alpha_dummy_666 x u D R S_cls f E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_693 D R S_cls E),
        (nb095_alpha_dummy_696 x u D R S_cls f E)), ((nb095_alpha_dummy_692 D R S_cls E),
        (nb095_alpha_dummy_695 x u D R S_cls f E)), ((nb095_alpha_dummy_691 D R S_cls E),
        (nb095_alpha_dummy_694 x u D R S_cls f E)), ((nb095_alpha_dummy_689 D R S_cls E),
        (nb095_alpha_dummy_690 x u D R S_cls f E)), ((nb095_alpha_dummy_685 D R S_cls E),
        (nb095_alpha_dummy_687 x u D R S_cls f E)), ((nb095_alpha_dummy_686 D R S_cls E),
        (nb095_alpha_dummy_688 x u D R S_cls f E)), ((nb095_alpha_dummy_711 D R S_cls E),
        (nb095_alpha_dummy_712 x u D R S_cls f E)), ((nb095_alpha_dummy_709 D R S_cls E),
        (nb095_alpha_dummy_710 x u D R S_cls f E)), ((nb095_alpha_dummy_678 D R S_cls E),
        (nb095_alpha_dummy_680 x u D R S_cls f E)), ((nb095_alpha_dummy_677 D R S_cls E),
        (nb095_alpha_dummy_679 x u D R S_cls f E)), ((nb095_alpha_dummy_707 D R S_cls E),
        (nb095_alpha_dummy_708 x u D R S_cls f E)), ((nb095_alpha_dummy_681 D R S_cls E),
        (nb095_alpha_dummy_682 x u D R S_cls f E)), ((nb095_alpha_dummy_669 D R S_cls E),
        (nb095_alpha_dummy_670 x u D R S_cls f E)), ((nb095_alpha_dummy_671 D R S_cls E),
        (nb095_alpha_dummy_672 x u D R S_cls f E)), ((nb095_alpha_dummy_674 D R S_cls E),
        (nb095_alpha_dummy_676 x u D R S_cls f E)), ((nb095_alpha_dummy_673 D R S_cls E),
        (nb095_alpha_dummy_675 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_667 D R S_cls E),
        (nb095_alpha_dummy_668 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
        (nb095_alpha_dummy_666 x u D R S_cls f E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_685 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_704 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_704 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_706 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_706 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_685 D R S_cls E) ≠
                                (nb095_alpha_dummy_689 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_689 D R S_cls E),
                              (nb095_alpha_dummy_690 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_685 D R S_cls E),
                              (nb095_alpha_dummy_687 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_686 D R S_cls E),
                              (nb095_alpha_dummy_688 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_711 D R S_cls E),
                              (nb095_alpha_dummy_712 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_709 D R S_cls E),
                              (nb095_alpha_dummy_710 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_678 D R S_cls E),
                              (nb095_alpha_dummy_680 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_677 D R S_cls E),
                              (nb095_alpha_dummy_679 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_707 D R S_cls E),
                              (nb095_alpha_dummy_708 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_681 D R S_cls E),
                              (nb095_alpha_dummy_682 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_669 D R S_cls E),
                              (nb095_alpha_dummy_670 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_671 D R S_cls E),
                              (nb095_alpha_dummy_672 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_674 D R S_cls E),
                              (nb095_alpha_dummy_676 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_673 D R S_cls E),
                              (nb095_alpha_dummy_675 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_662 D R S_cls E),
                              (nb095_alpha_dummy_664 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_661 D R S_cls E),
                              (nb095_alpha_dummy_663 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_667 D R S_cls E),
                              (nb095_alpha_dummy_668 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_665 D R S_cls E),
                              (nb095_alpha_dummy_666 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
                              (nb095_alpha_dummy_689 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_689;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0710 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_690;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_685 D R S_cls E) ≠
                                (nb095_alpha_dummy_689 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_689 D R S_cls E),
                              (nb095_alpha_dummy_690 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_685 D R S_cls E),
                              (nb095_alpha_dummy_687 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_686 D R S_cls E),
                              (nb095_alpha_dummy_688 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_711 D R S_cls E),
                              (nb095_alpha_dummy_712 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_709 D R S_cls E),
                              (nb095_alpha_dummy_710 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_678 D R S_cls E),
                              (nb095_alpha_dummy_680 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_677 D R S_cls E),
                              (nb095_alpha_dummy_679 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_707 D R S_cls E),
                              (nb095_alpha_dummy_708 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_681 D R S_cls E),
                              (nb095_alpha_dummy_682 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_669 D R S_cls E),
                              (nb095_alpha_dummy_670 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_671 D R S_cls E),
                              (nb095_alpha_dummy_672 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_674 D R S_cls E),
                              (nb095_alpha_dummy_676 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_673 D R S_cls E),
                              (nb095_alpha_dummy_675 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_662 D R S_cls E),
                              (nb095_alpha_dummy_664 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_661 D R S_cls E),
                              (nb095_alpha_dummy_663 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_667 D R S_cls E),
                              (nb095_alpha_dummy_668 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_665 D R S_cls E),
                              (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                        (nb095_alpha_dummy_685 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_685;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_687 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_687;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0709 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_678 D R S_cls E) ≠
                          (nb095_alpha_dummy_686 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_686;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0708 D R S_cls E)
                                  1)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_688 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_688;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0709 x u D R S_cls f E) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                            (nb095_alpha_dummy_711 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_711;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0738 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_712 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_712;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0739 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_678 D R S_cls E) ≠
                              (nb095_alpha_dummy_709 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_709;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0736 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_680 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_710 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_710;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0737 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_678 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_692 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_692;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0712 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_695 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_695;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0713 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_685 D R S_cls E) ≠ (nb095_alpha_dummy_691 D R S_cls E) from (by
          unfold nb095_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0712 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_694 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0713 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_685 D R S_cls E) ≠
        (nb095_alpha_dummy_689 D R S_cls E) from (by
          unfold nb095_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0710 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0711 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_693 D R S_cls E),
        (nb095_alpha_dummy_696 x u D R S_cls f E)), ((nb095_alpha_dummy_692 D R S_cls E),
        (nb095_alpha_dummy_695 x u D R S_cls f E)), ((nb095_alpha_dummy_691 D R S_cls E),
        (nb095_alpha_dummy_694 x u D R S_cls f E)), ((nb095_alpha_dummy_689 D R S_cls E),
        (nb095_alpha_dummy_690 x u D R S_cls f E)), ((nb095_alpha_dummy_685 D R S_cls E),
        (nb095_alpha_dummy_687 x u D R S_cls f E)), ((nb095_alpha_dummy_686 D R S_cls E),
        (nb095_alpha_dummy_688 x u D R S_cls f E)), ((nb095_alpha_dummy_711 D R S_cls E),
        (nb095_alpha_dummy_712 x u D R S_cls f E)), ((nb095_alpha_dummy_709 D R S_cls E),
        (nb095_alpha_dummy_710 x u D R S_cls f E)), ((nb095_alpha_dummy_678 D R S_cls E),
        (nb095_alpha_dummy_680 x u D R S_cls f E)), ((nb095_alpha_dummy_677 D R S_cls E),
        (nb095_alpha_dummy_679 x u D R S_cls f E)), ((nb095_alpha_dummy_707 D R S_cls E),
        (nb095_alpha_dummy_708 x u D R S_cls f E)), ((nb095_alpha_dummy_681 D R S_cls E),
        (nb095_alpha_dummy_682 x u D R S_cls f E)), ((nb095_alpha_dummy_669 D R S_cls E),
        (nb095_alpha_dummy_670 x u D R S_cls f E)), ((nb095_alpha_dummy_671 D R S_cls E),
        (nb095_alpha_dummy_672 x u D R S_cls f E)), ((nb095_alpha_dummy_674 D R S_cls E),
        (nb095_alpha_dummy_676 x u D R S_cls f E)), ((nb095_alpha_dummy_673 D R S_cls E),
        (nb095_alpha_dummy_675 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_667 D R S_cls E),
        (nb095_alpha_dummy_668 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
        (nb095_alpha_dummy_666 x u D R S_cls f E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_699 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0716
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0717
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0714
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0715
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_699 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0720
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_700 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0721
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_697 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_697;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0718
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_698 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_698;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0719
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_693 D R S_cls E), (nb095_alpha_dummy_696 x u D R S_cls f E)),
        ((nb095_alpha_dummy_692 D R S_cls E), (nb095_alpha_dummy_695 x u D R S_cls f E)),
        ((nb095_alpha_dummy_691 D R S_cls E), (nb095_alpha_dummy_694 x u D R S_cls f E)),
        ((nb095_alpha_dummy_689 D R S_cls E), (nb095_alpha_dummy_690 x u D R S_cls f E)),
        ((nb095_alpha_dummy_685 D R S_cls E), (nb095_alpha_dummy_687 x u D R S_cls f E)),
        ((nb095_alpha_dummy_686 D R S_cls E), (nb095_alpha_dummy_688 x u D R S_cls f E)),
        ((nb095_alpha_dummy_711 D R S_cls E), (nb095_alpha_dummy_712 x u D R S_cls f E)),
        ((nb095_alpha_dummy_709 D R S_cls E), (nb095_alpha_dummy_710 x u D R S_cls f E)),
        ((nb095_alpha_dummy_678 D R S_cls E), (nb095_alpha_dummy_680 x u D R S_cls f E)),
        ((nb095_alpha_dummy_677 D R S_cls E), (nb095_alpha_dummy_679 x u D R S_cls f E)),
        ((nb095_alpha_dummy_707 D R S_cls E), (nb095_alpha_dummy_708 x u D R S_cls f E)),
        ((nb095_alpha_dummy_681 D R S_cls E), (nb095_alpha_dummy_682 x u D R S_cls f E)),
        ((nb095_alpha_dummy_669 D R S_cls E), (nb095_alpha_dummy_670 x u D R S_cls f E)),
        ((nb095_alpha_dummy_671 D R S_cls E), (nb095_alpha_dummy_672 x u D R S_cls f E)),
        ((nb095_alpha_dummy_674 D R S_cls E), (nb095_alpha_dummy_676 x u D R S_cls f E)),
        ((nb095_alpha_dummy_673 D R S_cls E), (nb095_alpha_dummy_675 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_667 D R S_cls E), (nb095_alpha_dummy_668 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_685 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_692 D R S_cls E) ≠ (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_704 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_703 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0724
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_704 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0725
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_692 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0722
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_695 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0723
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_685
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_687 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_706 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_693 D R S_cls E) ≠ (nb095_alpha_dummy_705 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0728
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_706 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0729
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_693 D R S_cls E) ≠
        (nb095_alpha_dummy_701 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0726
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_696 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_702 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0727
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_685 D R S_cls E) ≠
                                  (nb095_alpha_dummy_689 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_689;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_690;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_689 D R S_cls E),
                                (nb095_alpha_dummy_690 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_685 D R S_cls E),
                                (nb095_alpha_dummy_687 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_686 D R S_cls E),
                                (nb095_alpha_dummy_688 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_711 D R S_cls E),
                                (nb095_alpha_dummy_712 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_709 D R S_cls E),
                                (nb095_alpha_dummy_710 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_678 D R S_cls E),
                                (nb095_alpha_dummy_680 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_677 D R S_cls E),
                                (nb095_alpha_dummy_679 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_707 D R S_cls E),
                                (nb095_alpha_dummy_708 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_681 D R S_cls E),
                                (nb095_alpha_dummy_682 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_669 D R S_cls E),
                                (nb095_alpha_dummy_670 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_671 D R S_cls E),
                                (nb095_alpha_dummy_672 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_674 D R S_cls E),
                                (nb095_alpha_dummy_676 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_673 D R S_cls E),
                                (nb095_alpha_dummy_675 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_662 D R S_cls E),
                                (nb095_alpha_dummy_664 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_661 D R S_cls E),
                                (nb095_alpha_dummy_663 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_667 D R S_cls E),
                                (nb095_alpha_dummy_668 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_665 D R S_cls E),
                                (nb095_alpha_dummy_666 x u D R S_cls f E)),
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
                              (nb095_alpha_dummy_685 D R S_cls E) ≠
                                (nb095_alpha_dummy_689 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_689;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_690;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_685 D R S_cls E) ≠
                                  (nb095_alpha_dummy_689 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_689;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0710 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_687 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_690 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_690;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0711 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_689 D R S_cls E),
                                (nb095_alpha_dummy_690 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_685 D R S_cls E),
                                (nb095_alpha_dummy_687 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_686 D R S_cls E),
                                (nb095_alpha_dummy_688 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_711 D R S_cls E),
                                (nb095_alpha_dummy_712 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_709 D R S_cls E),
                                (nb095_alpha_dummy_710 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_678 D R S_cls E),
                                (nb095_alpha_dummy_680 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_677 D R S_cls E),
                                (nb095_alpha_dummy_679 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_707 D R S_cls E),
                                (nb095_alpha_dummy_708 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_681 D R S_cls E),
                                (nb095_alpha_dummy_682 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_669 D R S_cls E),
                                (nb095_alpha_dummy_670 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_671 D R S_cls E),
                                (nb095_alpha_dummy_672 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_674 D R S_cls E),
                                (nb095_alpha_dummy_676 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_673 D R S_cls E),
                                (nb095_alpha_dummy_675 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_662 D R S_cls E),
                                (nb095_alpha_dummy_664 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_661 D R S_cls E),
                                (nb095_alpha_dummy_663 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_667 D R S_cls E),
                                (nb095_alpha_dummy_668 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_665 D R S_cls E),
                                (nb095_alpha_dummy_666 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
