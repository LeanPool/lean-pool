/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part038Stage1


/-! NF weak partition development: NAR4H5C095M3Part038. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0085`. -/
@[expose]
noncomputable def nb095SplitAlpha0085 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy631 D R S_cls E), (nb095AlphaDummy632 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy631 D R S_cls E))
          (Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy631 D R S_cls E))
            (Class.cab (nb095AlphaDummy625 D R S_cls E)
              (synWrex (nb095AlphaDummy626 D R S_cls E)
                (Class.cv (nb095AlphaDummy619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy632 x D R))
          (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy632 x D R))
            (Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
                (Class.cv (nb095AlphaDummy621 x D R))
                (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                  (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                      (nb095AlphaDummy626 D R S_cls E) from (by
                      unfold nb095AlphaDummy626;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
                  (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
                      unfold nb095AlphaDummy628;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                        (nb095AlphaDummy625 D R S_cls E) from (by
                        unfold nb095AlphaDummy625;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
                    (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy627 x D R) from (by
                        unfold nb095AlphaDummy627;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                          (nb095AlphaDummy631 D R S_cls E) from (by
                          unfold nb095AlphaDummy631;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0648 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy632 x D R) from
                        (by
                          unfold nb095AlphaDummy632;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0649 x D R) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                            (nb095AlphaDummy629 D R S_cls E) from (by
                            unfold nb095AlphaDummy629;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0645 D R S_cls E)
                                    0)))) (show
                          (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy630 x D R) from (by
                            unfold nb095AlphaDummy630;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0647 x D R) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCin D
                                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv
                                        (nb095AlphaDummy002 D R S_cls E)))))).fv ∪
                              ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                      (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((synCin D
                                  (synCima (synCcnv (synCdif R (synCid)))
                                    (synCsn (Class.cv x))))).fv ∪ ((synCin D
                                  (synCima (synCcnv (synCdif R (synCid)))
                                    (synCsn (Class.cv x))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
                      ((Class.cv (nb095AlphaDummy622 x D R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                              (nb095AlphaDummy633 D R S_cls E) from (by
                              unfold nb095AlphaDummy633;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E)
                                      0)))) (show
                            (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy635 x D R) from
                            (by
                              unfold nb095AlphaDummy635;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                                (nb095AlphaDummy634 D R S_cls E) from (by
                                unfold nb095AlphaDummy634;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0650 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy636 x D R) from
                              (by
                                unfold nb095AlphaDummy636;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy628 x D R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy640 D R S_cls E) from (by
          unfold nb095AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy643 x D R) from
        (by
          unfold nb095AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy639 D R S_cls E) from (by
          unfold nb095AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy642 x D R) from
        (by
          unfold nb095AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy637 D R S_cls E) from (by
          unfold nb095AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
        (by
          unfold nb095AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy641 D R S_cls E), (nb095AlphaDummy644 x D R)),
        ((nb095AlphaDummy640 D R S_cls E), (nb095AlphaDummy643 x D R)),
        ((nb095AlphaDummy639 D R S_cls E), (nb095AlphaDummy642 x D R)),
        ((nb095AlphaDummy637 D R S_cls E), (nb095AlphaDummy638 x D R)),
        ((nb095AlphaDummy633 D R S_cls E), (nb095AlphaDummy635 x D R)),
        ((nb095AlphaDummy634 D R S_cls E), (nb095AlphaDummy636 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy631 D R S_cls E), (nb095AlphaDummy632 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy640
        D R S_cls E) ≠ (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy641 D R S_cls E), (nb095AlphaDummy644 x D R)),
        ((nb095AlphaDummy640 D R S_cls E), (nb095AlphaDummy643 x D R)),
        ((nb095AlphaDummy639 D R S_cls E), (nb095AlphaDummy642 x D R)),
        ((nb095AlphaDummy637 D R S_cls E), (nb095AlphaDummy638 x D R)),
        ((nb095AlphaDummy633 D R S_cls E), (nb095AlphaDummy635 x D R)),
        ((nb095AlphaDummy634 D R S_cls E), (nb095AlphaDummy636 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy631 D R S_cls E), (nb095AlphaDummy632 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy640
        D R S_cls E) ≠ (nb095AlphaDummy651 D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy651
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641
        D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641
        D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy633 D R S_cls E) ≠
                                        (nb095AlphaDummy637 D R S_cls E) from (by
                                        unfold nb095AlphaDummy637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy635 x D R) ≠
                                        (nb095AlphaDummy638 x D R) from (by
                                        unfold nb095AlphaDummy638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy637 D R S_cls E),
                                      (nb095AlphaDummy638 x D R)),
                                    ((nb095AlphaDummy633 D R S_cls E),
                                      (nb095AlphaDummy635 x D R)),
                                    ((nb095AlphaDummy634 D R S_cls E),
                                      (nb095AlphaDummy636 x D R)),
                                    ((nb095AlphaDummy626 D R S_cls E),
                                      (nb095AlphaDummy628 x D R)),
                                    ((nb095AlphaDummy625 D R S_cls E),
                                      (nb095AlphaDummy627 x D R)),
                                    ((nb095AlphaDummy631 D R S_cls E),
                                      (nb095AlphaDummy632 x D R)),
                                    ((nb095AlphaDummy629 D R S_cls E),
                                      (nb095AlphaDummy630 x D R)),
                                    ((nb095AlphaDummy620 D R S_cls E),
                                      (nb095AlphaDummy622 x D R)),
                                    ((nb095AlphaDummy619 D R S_cls E),
                                      (nb095AlphaDummy621 x D R)),
                                    ((nb095AlphaDummy623 D R S_cls E),
                                      (nb095AlphaDummy624 x D R)),
                                    ((nb095AlphaDummy617 D R S_cls E),
                                      (nb095AlphaDummy618 x D R)),
                                    ((nb095AlphaDummy615 D R S_cls E),
                                      (nb095AlphaDummy616 x D R)),
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
                                    (nb095AlphaDummy633 D R S_cls E) ≠
                                      (nb095AlphaDummy637 D R S_cls E) from (by
                                      unfold nb095AlphaDummy637;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy635 x D R) ≠
                                      (nb095AlphaDummy638 x D R) from (by
                                      unfold nb095AlphaDummy638;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0653 x D R) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy633 D R S_cls E) ≠
                                        (nb095AlphaDummy637 D R S_cls E) from (by
                                        unfold nb095AlphaDummy637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy635 x D R) ≠
                                        (nb095AlphaDummy638 x D R) from (by
                                        unfold nb095AlphaDummy638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy637 D R S_cls E),
                                      (nb095AlphaDummy638 x D R)),
                                    ((nb095AlphaDummy633 D R S_cls E),
                                      (nb095AlphaDummy635 x D R)),
                                    ((nb095AlphaDummy634 D R S_cls E),
                                      (nb095AlphaDummy636 x D R)),
                                    ((nb095AlphaDummy626 D R S_cls E),
                                      (nb095AlphaDummy628 x D R)),
                                    ((nb095AlphaDummy625 D R S_cls E),
                                      (nb095AlphaDummy627 x D R)),
                                    ((nb095AlphaDummy631 D R S_cls E),
                                      (nb095AlphaDummy632 x D R)),
                                    ((nb095AlphaDummy629 D R S_cls E),
                                      (nb095AlphaDummy630 x D R)),
                                    ((nb095AlphaDummy620 D R S_cls E),
                                      (nb095AlphaDummy622 x D R)),
                                    ((nb095AlphaDummy619 D R S_cls E),
                                      (nb095AlphaDummy621 x D R)),
                                    ((nb095AlphaDummy623 D R S_cls E),
                                      (nb095AlphaDummy624 x D R)),
                                    ((nb095AlphaDummy617 D R S_cls E),
                                      (nb095AlphaDummy618 x D R)),
                                    ((nb095AlphaDummy615 D R S_cls E),
                                      (nb095AlphaDummy616 x D R)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                        (nb095AlphaDummy626 D R S_cls E) from (by
                        unfold nb095AlphaDummy626;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
                    (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy628 x D R) from (by
                        unfold nb095AlphaDummy628;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                          (nb095AlphaDummy625 D R S_cls E) from (by
                          unfold nb095AlphaDummy625;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy627 x D R) from
                        (by
                          unfold nb095AlphaDummy627;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                            (nb095AlphaDummy631 D R S_cls E) from (by
                            unfold nb095AlphaDummy631;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0648 D R S_cls E)
                                    0)))) (show
                          (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy632 x D R) from (by
                            unfold nb095AlphaDummy632;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0649 x D R) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy619 D R S_cls E) ≠
                              (nb095AlphaDummy629 D R S_cls E) from (by
                              unfold nb095AlphaDummy629;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0645 D R S_cls E)
                                      0)))) (show
                            (nb095AlphaDummy621 x D R) ≠ (nb095AlphaDummy630 x D R) from
                            (by
                              unfold nb095AlphaDummy630;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0647 x D R) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCin D
                                    (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪
                                ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                                        (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
                              (by decide)) (freshVar_injective (((synCin D
                                    (synCima (synCcnv (synCdif R (synCid)))
                                      (synCsn (Class.cv x))))).fv ∪ ((synCin D
                                    (synCima (synCcnv (synCdif R (synCid)))
                                      (synCsn (Class.cv x))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy619 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy620 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy621 x D R))).fv ∪
                        ((Class.cv (nb095AlphaDummy622 x D R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy626 D R S_cls E) ≠
                                (nb095AlphaDummy633 D R S_cls E) from (by
                                unfold nb095AlphaDummy633;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0650 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy635 x D R) from
                              (by
                                unfold nb095AlphaDummy635;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                        0)))) (TAlphaVar.there (show
                                (nb095AlphaDummy626 D R S_cls E) ≠
                                  (nb095AlphaDummy634 D R S_cls E) from (by
                                  unfold nb095AlphaDummy634;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0650 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy636 x D R)
                                from (by
                                  unfold nb095AlphaDummy636;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy628 x D R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy633 D R S_cls E) ≠ (nb095AlphaDummy640 D R S_cls E) from (by
          unfold nb095AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy643 x D R) from
        (by
          unfold nb095AlphaDummy643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy639 D R S_cls E) from (by
          unfold nb095AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy642 x D R) from
        (by
          unfold nb095AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy637 D R S_cls E) from (by
          unfold nb095AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
        (by
          unfold nb095AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy641 D R S_cls E), (nb095AlphaDummy644 x D R)),
        ((nb095AlphaDummy640 D R S_cls E), (nb095AlphaDummy643 x D R)),
        ((nb095AlphaDummy639 D R S_cls E), (nb095AlphaDummy642 x D R)),
        ((nb095AlphaDummy637 D R S_cls E), (nb095AlphaDummy638 x D R)),
        ((nb095AlphaDummy633 D R S_cls E), (nb095AlphaDummy635 x D R)),
        ((nb095AlphaDummy634 D R S_cls E), (nb095AlphaDummy636 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy631 D R S_cls E), (nb095AlphaDummy632 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy640
        D R S_cls E) ≠ (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy641 D R S_cls E), (nb095AlphaDummy644 x D R)),
        ((nb095AlphaDummy640 D R S_cls E), (nb095AlphaDummy643 x D R)),
        ((nb095AlphaDummy639 D R S_cls E), (nb095AlphaDummy642 x D R)),
        ((nb095AlphaDummy637 D R S_cls E), (nb095AlphaDummy638 x D R)),
        ((nb095AlphaDummy633 D R S_cls E), (nb095AlphaDummy635 x D R)),
        ((nb095AlphaDummy634 D R S_cls E), (nb095AlphaDummy636 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy631 D R S_cls E), (nb095AlphaDummy632 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy640
        D R S_cls E) ≠ (nb095AlphaDummy651 D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy651
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641
        D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641
        D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy637 D R S_cls E) from (by
                                          unfold nb095AlphaDummy637;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0652 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy635 x D R) ≠
        (nb095AlphaDummy638 x D R) from (by
                                          unfold nb095AlphaDummy638;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0653 x D R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy637 D R S_cls E),
                                        (nb095AlphaDummy638 x D R)),
                                      ((nb095AlphaDummy633 D R S_cls E),
                                        (nb095AlphaDummy635 x D R)),
                                      ((nb095AlphaDummy634 D R S_cls E),
                                        (nb095AlphaDummy636 x D R)),
                                      ((nb095AlphaDummy626 D R S_cls E),
                                        (nb095AlphaDummy628 x D R)),
                                      ((nb095AlphaDummy625 D R S_cls E),
                                        (nb095AlphaDummy627 x D R)),
                                      ((nb095AlphaDummy631 D R S_cls E),
                                        (nb095AlphaDummy632 x D R)),
                                      ((nb095AlphaDummy629 D R S_cls E),
                                        (nb095AlphaDummy630 x D R)),
                                      ((nb095AlphaDummy620 D R S_cls E),
                                        (nb095AlphaDummy622 x D R)),
                                      ((nb095AlphaDummy619 D R S_cls E),
                                        (nb095AlphaDummy621 x D R)),
                                      ((nb095AlphaDummy623 D R S_cls E),
                                        (nb095AlphaDummy624 x D R)),
                                      ((nb095AlphaDummy617 D R S_cls E),
                                        (nb095AlphaDummy618 x D R)),
                                      ((nb095AlphaDummy615 D R S_cls E),
                                        (nb095AlphaDummy616 x D R)),
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
                                      (nb095AlphaDummy633 D R S_cls E) ≠
                                        (nb095AlphaDummy637 D R S_cls E) from (by
                                        unfold nb095AlphaDummy637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy635 x D R) ≠
                                        (nb095AlphaDummy638 x D R) from (by
                                        unfold nb095AlphaDummy638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy637 D R S_cls E) from (by
                                          unfold nb095AlphaDummy637;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0652 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy635 x D R) ≠
        (nb095AlphaDummy638 x D R) from (by
                                          unfold nb095AlphaDummy638;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0653 x D R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy637 D R S_cls E),
                                        (nb095AlphaDummy638 x D R)),
                                      ((nb095AlphaDummy633 D R S_cls E),
                                        (nb095AlphaDummy635 x D R)),
                                      ((nb095AlphaDummy634 D R S_cls E),
                                        (nb095AlphaDummy636 x D R)),
                                      ((nb095AlphaDummy626 D R S_cls E),
                                        (nb095AlphaDummy628 x D R)),
                                      ((nb095AlphaDummy625 D R S_cls E),
                                        (nb095AlphaDummy627 x D R)),
                                      ((nb095AlphaDummy631 D R S_cls E),
                                        (nb095AlphaDummy632 x D R)),
                                      ((nb095AlphaDummy629 D R S_cls E),
                                        (nb095AlphaDummy630 x D R)),
                                      ((nb095AlphaDummy620 D R S_cls E),
                                        (nb095AlphaDummy622 x D R)),
                                      ((nb095AlphaDummy619 D R S_cls E),
                                        (nb095AlphaDummy621 x D R)),
                                      ((nb095AlphaDummy623 D R S_cls E),
                                        (nb095AlphaDummy624 x D R)),
                                      ((nb095AlphaDummy617 D R S_cls E),
                                        (nb095AlphaDummy618 x D R)),
                                      ((nb095AlphaDummy615 D R S_cls E),
                                        (nb095AlphaDummy616 x D R)),
                                      ((nb095AlphaDummy004 D R S_cls E),
                                        (nb095AlphaDummy006 x u D R S_cls f E)),
                                      ((nb095AlphaDummy003 D R S_cls E),
                                        (nb095AlphaDummy005 x u D R S_cls f E)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0086`. -/
@[expose]
noncomputable def nb095SplitAlpha0086 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy659 D R S_cls E), (nb095AlphaDummy660 x D R)),
        ((nb095AlphaDummy657 D R S_cls E), (nb095AlphaDummy658 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy655 D R S_cls E), (nb095AlphaDummy656 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy659 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy659 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy660 x D R))
          (synCphi (Class.cv (nb095AlphaDummy628 x D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy660 x D R))
            (synCphi (Class.cv (nb095AlphaDummy628 x D R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                      (nb095AlphaDummy633 D R S_cls E) from (by
                      unfold nb095AlphaDummy633;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 0))))
                  (show (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy635 x D R) from (by
                      unfold nb095AlphaDummy635;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                        (nb095AlphaDummy634 D R S_cls E) from (by
                        unfold nb095AlphaDummy634;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 1))))
                    (show (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy636 x D R) from (by
                        unfold nb095AlphaDummy636;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0651 x D R) 1))))
                    (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                          (nb095AlphaDummy659 D R S_cls E) from (by
                          unfold nb095AlphaDummy659;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0680 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy660 x D R) from
                        (by
                          unfold nb095AlphaDummy660;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0681 x D R) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                            (nb095AlphaDummy657 D R S_cls E) from (by
                            unfold nb095AlphaDummy657;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0678 D R S_cls E)
                                    0)))) (show
                          (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy658 x D R) from (by
                            unfold nb095AlphaDummy658;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0679 x D R) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy628 x D R))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy633 D R S_cls E) ≠
                                        (nb095AlphaDummy640 D R S_cls E) from (by
                                        unfold nb095AlphaDummy640;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0654 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy635 x D R) ≠
                                        (nb095AlphaDummy643 x D R) from (by
                                        unfold nb095AlphaDummy643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0655 x D R) 1))))
                                    (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy639 D R S_cls E) from (by
                                          unfold nb095AlphaDummy639;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0654 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy635 x D R) ≠
        (nb095AlphaDummy642 x D R) from (by
                                          unfold nb095AlphaDummy642;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0655 x D R) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy633 D R S_cls E) ≠ (nb095AlphaDummy637 D R S_cls E) from (by
          unfold nb095AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
        (by
          unfold nb095AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy641 D R S_cls E),
        (nb095AlphaDummy644 x D R)), ((nb095AlphaDummy640 D R S_cls E),
        (nb095AlphaDummy643 x D R)), ((nb095AlphaDummy639 D R S_cls E),
        (nb095AlphaDummy642 x D R)), ((nb095AlphaDummy637 D R S_cls E),
        (nb095AlphaDummy638 x D R)), ((nb095AlphaDummy633 D R S_cls E),
        (nb095AlphaDummy635 x D R)), ((nb095AlphaDummy634 D R S_cls E),
        (nb095AlphaDummy636 x D R)), ((nb095AlphaDummy659 D R S_cls E),
        (nb095AlphaDummy660 x D R)), ((nb095AlphaDummy657 D R S_cls E),
        (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy641 D R S_cls E),
        (nb095AlphaDummy644 x D R)), ((nb095AlphaDummy640 D R S_cls E),
        (nb095AlphaDummy643 x D R)), ((nb095AlphaDummy639 D R S_cls E),
        (nb095AlphaDummy642 x D R)), ((nb095AlphaDummy637 D R S_cls E),
        (nb095AlphaDummy638 x D R)), ((nb095AlphaDummy633 D R S_cls E),
        (nb095AlphaDummy635 x D R)), ((nb095AlphaDummy634 D R S_cls E),
        (nb095AlphaDummy636 x D R)), ((nb095AlphaDummy659 D R S_cls E),
        (nb095AlphaDummy660 x D R)), ((nb095AlphaDummy657 D R S_cls E),
        (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy633 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy651 D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy651 D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy633 D R S_cls E) ≠
                                (nb095AlphaDummy637 D R S_cls E) from (by
                                unfold nb095AlphaDummy637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
                              (by
                                unfold nb095AlphaDummy638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed [((nb095AlphaDummy637 D R S_cls E),
                              (nb095AlphaDummy638 x D R)),
                            ((nb095AlphaDummy633 D R S_cls E),
                              (nb095AlphaDummy635 x D R)),
                            ((nb095AlphaDummy634 D R S_cls E),
                              (nb095AlphaDummy636 x D R)),
                            ((nb095AlphaDummy659 D R S_cls E),
                              (nb095AlphaDummy660 x D R)),
                            ((nb095AlphaDummy657 D R S_cls E),
                              (nb095AlphaDummy658 x D R)),
                            ((nb095AlphaDummy626 D R S_cls E),
                              (nb095AlphaDummy628 x D R)),
                            ((nb095AlphaDummy625 D R S_cls E),
                              (nb095AlphaDummy627 x D R)),
                            ((nb095AlphaDummy655 D R S_cls E),
                              (nb095AlphaDummy656 x D R)),
                            ((nb095AlphaDummy629 D R S_cls E),
                              (nb095AlphaDummy630 x D R)),
                            ((nb095AlphaDummy620 D R S_cls E),
                              (nb095AlphaDummy622 x D R)),
                            ((nb095AlphaDummy619 D R S_cls E),
                              (nb095AlphaDummy621 x D R)),
                            ((nb095AlphaDummy623 D R S_cls E),
                              (nb095AlphaDummy624 x D R)),
                            ((nb095AlphaDummy617 D R S_cls E),
                              (nb095AlphaDummy618 x D R)),
                            ((nb095AlphaDummy615 D R S_cls E),
                              (nb095AlphaDummy616 x D R)),
                            ((nb095AlphaDummy004 D R S_cls E),
                              (nb095AlphaDummy006 x u D R S_cls f E)),
                            ((nb095AlphaDummy003 D R S_cls E),
                              (nb095AlphaDummy005 x u D R S_cls f E)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
                              (nb095AlphaDummy637 D R S_cls E) from (by
                              unfold nb095AlphaDummy637;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0652 D R S_cls E)
                                      0)))) (show
                            (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
                            (by
                              unfold nb095AlphaDummy638;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0653 x D R) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy633 D R S_cls E) ≠
                                (nb095AlphaDummy637 D R S_cls E) from (by
                                unfold nb095AlphaDummy637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
                              (by
                                unfold nb095AlphaDummy638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed [((nb095AlphaDummy637 D R S_cls E),
                              (nb095AlphaDummy638 x D R)),
                            ((nb095AlphaDummy633 D R S_cls E),
                              (nb095AlphaDummy635 x D R)),
                            ((nb095AlphaDummy634 D R S_cls E),
                              (nb095AlphaDummy636 x D R)),
                            ((nb095AlphaDummy659 D R S_cls E),
                              (nb095AlphaDummy660 x D R)),
                            ((nb095AlphaDummy657 D R S_cls E),
                              (nb095AlphaDummy658 x D R)),
                            ((nb095AlphaDummy626 D R S_cls E),
                              (nb095AlphaDummy628 x D R)),
                            ((nb095AlphaDummy625 D R S_cls E),
                              (nb095AlphaDummy627 x D R)),
                            ((nb095AlphaDummy655 D R S_cls E),
                              (nb095AlphaDummy656 x D R)),
                            ((nb095AlphaDummy629 D R S_cls E),
                              (nb095AlphaDummy630 x D R)),
                            ((nb095AlphaDummy620 D R S_cls E),
                              (nb095AlphaDummy622 x D R)),
                            ((nb095AlphaDummy619 D R S_cls E),
                              (nb095AlphaDummy621 x D R)),
                            ((nb095AlphaDummy623 D R S_cls E),
                              (nb095AlphaDummy624 x D R)),
                            ((nb095AlphaDummy617 D R S_cls E),
                              (nb095AlphaDummy618 x D R)),
                            ((nb095AlphaDummy615 D R S_cls E),
                              (nb095AlphaDummy616 x D R)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                        (nb095AlphaDummy633 D R S_cls E) from (by
                        unfold nb095AlphaDummy633;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 0))))
                    (show (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy635 x D R) from (by
                        unfold nb095AlphaDummy635;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                    (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                          (nb095AlphaDummy634 D R S_cls E) from (by
                          unfold nb095AlphaDummy634;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E)
                                  1))))
                      (show (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy636 x D R) from
                        (by
                          unfold nb095AlphaDummy636;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0651 x D R) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                            (nb095AlphaDummy659 D R S_cls E) from (by
                            unfold nb095AlphaDummy659;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0680 D R S_cls E)
                                    0)))) (show
                          (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy660 x D R) from (by
                            unfold nb095AlphaDummy660;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0681 x D R) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy626 D R S_cls E) ≠
                              (nb095AlphaDummy657 D R S_cls E) from (by
                              unfold nb095AlphaDummy657;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0678 D R S_cls E)
                                      0)))) (show
                            (nb095AlphaDummy628 x D R) ≠ (nb095AlphaDummy658 x D R) from
                            (by
                              unfold nb095AlphaDummy658;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0679 x D R) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy626 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy628 x D R))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy633 D R S_cls E) ≠
        (nb095AlphaDummy640 D R S_cls E) from (by
                                          unfold nb095AlphaDummy640;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0654 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy635 x D R) ≠
        (nb095AlphaDummy643 x D R) from (by
                                          unfold nb095AlphaDummy643;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0655 x D R) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy633 D R S_cls E) ≠ (nb095AlphaDummy639 D R S_cls E) from (by
          unfold nb095AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy642 x D R) from
        (by
          unfold nb095AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy633 D R S_cls E) ≠ (nb095AlphaDummy637 D R S_cls E) from (by
          unfold nb095AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R S_cls E)
                  0)))) (show (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
        (by
          unfold nb095AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy641 D R S_cls E),
        (nb095AlphaDummy644 x D R)), ((nb095AlphaDummy640 D R S_cls E),
        (nb095AlphaDummy643 x D R)), ((nb095AlphaDummy639 D R S_cls E),
        (nb095AlphaDummy642 x D R)), ((nb095AlphaDummy637 D R S_cls E),
        (nb095AlphaDummy638 x D R)), ((nb095AlphaDummy633 D R S_cls E),
        (nb095AlphaDummy635 x D R)), ((nb095AlphaDummy634 D R S_cls E),
        (nb095AlphaDummy636 x D R)), ((nb095AlphaDummy659 D R S_cls E),
        (nb095AlphaDummy660 x D R)), ((nb095AlphaDummy657 D R S_cls E),
        (nb095AlphaDummy658 x D R)), ((nb095AlphaDummy626 D R S_cls E),
        (nb095AlphaDummy628 x D R)), ((nb095AlphaDummy625 D R S_cls E),
        (nb095AlphaDummy627 x D R)), ((nb095AlphaDummy655 D R S_cls E),
        (nb095AlphaDummy656 x D R)), ((nb095AlphaDummy629 D R S_cls E),
        (nb095AlphaDummy630 x D R)), ((nb095AlphaDummy620 D R S_cls E),
        (nb095AlphaDummy622 x D R)), ((nb095AlphaDummy619 D R S_cls E),
        (nb095AlphaDummy621 x D R)), ((nb095AlphaDummy623 D R S_cls E),
        (nb095AlphaDummy624 x D R)), ((nb095AlphaDummy617 D R S_cls E),
        (nb095AlphaDummy618 x D R)), ((nb095AlphaDummy615 D R S_cls E),
        (nb095AlphaDummy616 x D R)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647 D R S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy647 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy647 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy648 x D R) from
        (by
          unfold
            nb095AlphaDummy648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy645 D R S_cls E) from (by
          unfold
            nb095AlphaDummy645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy646 x D R) from
        (by
          unfold
            nb095AlphaDummy646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy641 D R S_cls E), (nb095AlphaDummy644 x D R)),
        ((nb095AlphaDummy640 D R S_cls E), (nb095AlphaDummy643 x D R)),
        ((nb095AlphaDummy639 D R S_cls E), (nb095AlphaDummy642 x D R)),
        ((nb095AlphaDummy637 D R S_cls E), (nb095AlphaDummy638 x D R)),
        ((nb095AlphaDummy633 D R S_cls E), (nb095AlphaDummy635 x D R)),
        ((nb095AlphaDummy634 D R S_cls E), (nb095AlphaDummy636 x D R)),
        ((nb095AlphaDummy659 D R S_cls E), (nb095AlphaDummy660 x D R)),
        ((nb095AlphaDummy657 D R S_cls E), (nb095AlphaDummy658 x D R)),
        ((nb095AlphaDummy626 D R S_cls E), (nb095AlphaDummy628 x D R)),
        ((nb095AlphaDummy625 D R S_cls E), (nb095AlphaDummy627 x D R)),
        ((nb095AlphaDummy655 D R S_cls E), (nb095AlphaDummy656 x D R)),
        ((nb095AlphaDummy629 D R S_cls E), (nb095AlphaDummy630 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy633 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy651 D R S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠ (nb095AlphaDummy651 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy652 x D R) from
        (by
          unfold
            nb095AlphaDummy652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy640 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy643 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy633
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy635 x D R))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy641 D R S_cls E) ≠ (nb095AlphaDummy653 D R S_cls E) from (by
          unfold
            nb095AlphaDummy653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy654 x D R) from
        (by
          unfold
            nb095AlphaDummy654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy641 D R S_cls E) ≠
        (nb095AlphaDummy649 D R S_cls E) from (by
          unfold
            nb095AlphaDummy649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy644 x D R) ≠ (nb095AlphaDummy650 x D R) from
        (by
          unfold
            nb095AlphaDummy650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy633 D R S_cls E) ≠
                                  (nb095AlphaDummy637 D R S_cls E) from (by
                                  unfold nb095AlphaDummy637;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R)
                                from (by
                                  unfold nb095AlphaDummy638;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed [((nb095AlphaDummy637 D R S_cls E),
                                (nb095AlphaDummy638 x D R)),
                              ((nb095AlphaDummy633 D R S_cls E),
                                (nb095AlphaDummy635 x D R)),
                              ((nb095AlphaDummy634 D R S_cls E),
                                (nb095AlphaDummy636 x D R)),
                              ((nb095AlphaDummy659 D R S_cls E),
                                (nb095AlphaDummy660 x D R)),
                              ((nb095AlphaDummy657 D R S_cls E),
                                (nb095AlphaDummy658 x D R)),
                              ((nb095AlphaDummy626 D R S_cls E),
                                (nb095AlphaDummy628 x D R)),
                              ((nb095AlphaDummy625 D R S_cls E),
                                (nb095AlphaDummy627 x D R)),
                              ((nb095AlphaDummy655 D R S_cls E),
                                (nb095AlphaDummy656 x D R)),
                              ((nb095AlphaDummy629 D R S_cls E),
                                (nb095AlphaDummy630 x D R)),
                              ((nb095AlphaDummy620 D R S_cls E),
                                (nb095AlphaDummy622 x D R)),
                              ((nb095AlphaDummy619 D R S_cls E),
                                (nb095AlphaDummy621 x D R)),
                              ((nb095AlphaDummy623 D R S_cls E),
                                (nb095AlphaDummy624 x D R)),
                              ((nb095AlphaDummy617 D R S_cls E),
                                (nb095AlphaDummy618 x D R)),
                              ((nb095AlphaDummy615 D R S_cls E),
                                (nb095AlphaDummy616 x D R)),
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
                              (nb095AlphaDummy633 D R S_cls E) ≠
                                (nb095AlphaDummy637 D R S_cls E) from (by
                                unfold nb095AlphaDummy637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R) from
                              (by
                                unfold nb095AlphaDummy638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy633 D R S_cls E) ≠
                                  (nb095AlphaDummy637 D R S_cls E) from (by
                                  unfold nb095AlphaDummy637;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy635 x D R) ≠ (nb095AlphaDummy638 x D R)
                                from (by
                                  unfold nb095AlphaDummy638;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed [((nb095AlphaDummy637 D R S_cls E),
                                (nb095AlphaDummy638 x D R)),
                              ((nb095AlphaDummy633 D R S_cls E),
                                (nb095AlphaDummy635 x D R)),
                              ((nb095AlphaDummy634 D R S_cls E),
                                (nb095AlphaDummy636 x D R)),
                              ((nb095AlphaDummy659 D R S_cls E),
                                (nb095AlphaDummy660 x D R)),
                              ((nb095AlphaDummy657 D R S_cls E),
                                (nb095AlphaDummy658 x D R)),
                              ((nb095AlphaDummy626 D R S_cls E),
                                (nb095AlphaDummy628 x D R)),
                              ((nb095AlphaDummy625 D R S_cls E),
                                (nb095AlphaDummy627 x D R)),
                              ((nb095AlphaDummy655 D R S_cls E),
                                (nb095AlphaDummy656 x D R)),
                              ((nb095AlphaDummy629 D R S_cls E),
                                (nb095AlphaDummy630 x D R)),
                              ((nb095AlphaDummy620 D R S_cls E),
                                (nb095AlphaDummy622 x D R)),
                              ((nb095AlphaDummy619 D R S_cls E),
                                (nb095AlphaDummy621 x D R)),
                              ((nb095AlphaDummy623 D R S_cls E),
                                (nb095AlphaDummy624 x D R)),
                              ((nb095AlphaDummy617 D R S_cls E),
                                (nb095AlphaDummy618 x D R)),
                              ((nb095AlphaDummy615 D R S_cls E),
                                (nb095AlphaDummy616 x D R)),
                              ((nb095AlphaDummy004 D R S_cls E),
                                (nb095AlphaDummy006 x u D R S_cls f E)),
                              ((nb095AlphaDummy003 D R S_cls E),
                                (nb095AlphaDummy005 x u D R S_cls f E)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb095_focused_notmem_0056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy620 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0057 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy622 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0058 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy619 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0059 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy621 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy623 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb095AlphaDummy619 D R S_cls E)} : Finset Var) ∪
            ({(nb095AlphaDummy620 D R S_cls E)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
              (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095AlphaDummy619 D R S_cls E)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))
      (Wff.classMem (Class.cv (nb095AlphaDummy620 D R S_cls E)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095AlphaDummy619 D R S_cls E))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0061 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy624 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb095AlphaDummy621 x D R)} : Finset Var) ∪
            ({(nb095AlphaDummy622 x D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
              (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095AlphaDummy621 x D R))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy622 x D R))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095AlphaDummy621 x D R))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0062 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy617 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0063 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy618 x D R) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy615 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
          ((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0065 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy616 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin R (synCxp (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv x))))))).fv ∪ ((synCnin R (synCxp (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (Class.cv x))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0298 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095AlphaDummy247 D R S_cls E), (nb095AlphaDummy248 x D R)),
        ((nb095AlphaDummy245 D R S_cls E), (nb095AlphaDummy246 x D R)),
        ((nb095AlphaDummy620 D R S_cls E), (nb095AlphaDummy622 x D R)),
        ((nb095AlphaDummy619 D R S_cls E), (nb095AlphaDummy621 x D R)),
        ((nb095AlphaDummy623 D R S_cls E), (nb095AlphaDummy624 x D R)),
        ((nb095AlphaDummy617 D R S_cls E), (nb095AlphaDummy618 x D R)),
        ((nb095AlphaDummy615 D R S_cls E), (nb095AlphaDummy616 x D R)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy247 D R S_cls E) (nb095AlphaDummy248 x D R)
      (nb095_focused_notmem_0005 D R S_cls E) (nb095_focused_notmem_0006 x D R)
      (TEnvFresh.consFresh (nb095AlphaDummy245 D R S_cls E)
        (nb095AlphaDummy246 x D R) (nb095_focused_notmem_0007 D R S_cls E)
        (nb095_focused_notmem_0008 x D R)
        (TEnvFresh.consFresh (nb095AlphaDummy620 D R S_cls E)
          (nb095AlphaDummy622 x D R) (nb095_focused_notmem_0056 D R S_cls E)
          (nb095_focused_notmem_0057 x D R)
          (TEnvFresh.consFresh (nb095AlphaDummy619 D R S_cls E)
            (nb095AlphaDummy621 x D R) (nb095_focused_notmem_0058 D R S_cls E)
            (nb095_focused_notmem_0059 x D R)
            (TEnvFresh.consFresh (nb095AlphaDummy623 D R S_cls E)
              (nb095AlphaDummy624 x D R) (nb095_focused_notmem_0060 D R S_cls E)
              (nb095_focused_notmem_0061 x D R)
              (TEnvFresh.consFresh (nb095AlphaDummy617 D R S_cls E)
                (nb095AlphaDummy618 x D R) (nb095_focused_notmem_0062 D R S_cls E)
                (nb095_focused_notmem_0063 x D R)
                (TEnvFresh.consFresh (nb095AlphaDummy615 D R S_cls E)
                  (nb095AlphaDummy616 x D R) (nb095_focused_notmem_0064 D R S_cls E)
                  (nb095_focused_notmem_0065 x D R)
                  (TEnvFresh.consFresh (nb095AlphaDummy004 D R S_cls E)
                    (nb095AlphaDummy006 x u D R S_cls f E)
                    (nb095_focused_notmem_0048 D R S_cls E)
                    (nb095_focused_notmem_0049 x u D R S_cls f E)
                    (TEnvFresh.consFresh (nb095AlphaDummy003 D R S_cls E)
                      (nb095AlphaDummy005 x u D R S_cls f E)
                      (nb095_focused_notmem_0044 D R S_cls E)
                      (nb095_focused_notmem_0045 x u D R S_cls f E)
                      (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
                        (nb095_focused_notmem_0009 D R S_cls E) dv_D_u
                        (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
                          (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
                          (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
                            (nb095_focused_notmem_0001 D R S_cls E) dv_D_f
                            (TEnvFresh.nil D.fv)))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
