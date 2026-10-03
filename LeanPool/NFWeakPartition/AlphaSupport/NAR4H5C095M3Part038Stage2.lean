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

@[expose]
noncomputable def nb095_split_alpha_0085 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_631 D R S_cls E), (nb095_alpha_dummy_632 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_631 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_631 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_625 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_626 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_625 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_632 x D R))
          (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
              (Class.cv (nb095_alpha_dummy_621 x D R))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_632 x D R))
            (Class.cab (nb095_alpha_dummy_627 x D R) (syn_wrex (nb095_alpha_dummy_628 x D R)
                (Class.cv (nb095_alpha_dummy_621 x D R))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_627 x D R))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                      (nb095_alpha_dummy_626 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_626;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
                      unfold nb095_alpha_dummy_628;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                        (nb095_alpha_dummy_625 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_625;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_627 x D R) from (by
                        unfold nb095_alpha_dummy_627;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                          (nb095_alpha_dummy_631 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_631;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0648 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_632 x D R) from
                        (by
                          unfold nb095_alpha_dummy_632;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0649 x D R) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                            (nb095_alpha_dummy_629 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_629;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0645 D R S_cls E)
                                    0)))) (show
                          (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_630 x D R) from (by
                            unfold nb095_alpha_dummy_630;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0647 x D R) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_cin D
                                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv
                                        (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪
                              ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                      (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
                            (by decide)) (freshVar_injective (((syn_cin D
                                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                    (syn_csn (Class.cv x))))).fv ∪ ((syn_cin D
                                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                    (syn_csn (Class.cv x))))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                              (nb095_alpha_dummy_633 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_633;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E)
                                      0)))) (show
                            (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_635 x D R) from
                            (by
                              unfold nb095_alpha_dummy_635;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                                (nb095_alpha_dummy_634 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_634;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0650 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_636 x D R) from
                              (by
                                unfold nb095_alpha_dummy_636;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_640 D R S_cls E) from (by
          unfold nb095_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_643 x D R) from
        (by
          unfold nb095_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_639 D R S_cls E) from (by
          unfold nb095_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_642 x D R) from
        (by
          unfold nb095_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_637 D R S_cls E) from (by
          unfold nb095_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
        (by
          unfold nb095_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_641 D R S_cls E), (nb095_alpha_dummy_644 x D R)),
        ((nb095_alpha_dummy_640 D R S_cls E), (nb095_alpha_dummy_643 x D R)),
        ((nb095_alpha_dummy_639 D R S_cls E), (nb095_alpha_dummy_642 x D R)),
        ((nb095_alpha_dummy_637 D R S_cls E), (nb095_alpha_dummy_638 x D R)),
        ((nb095_alpha_dummy_633 D R S_cls E), (nb095_alpha_dummy_635 x D R)),
        ((nb095_alpha_dummy_634 D R S_cls E), (nb095_alpha_dummy_636 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_631 D R S_cls E), (nb095_alpha_dummy_632 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_640
        D R S_cls E) ≠ (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_641 D R S_cls E), (nb095_alpha_dummy_644 x D R)),
        ((nb095_alpha_dummy_640 D R S_cls E), (nb095_alpha_dummy_643 x D R)),
        ((nb095_alpha_dummy_639 D R S_cls E), (nb095_alpha_dummy_642 x D R)),
        ((nb095_alpha_dummy_637 D R S_cls E), (nb095_alpha_dummy_638 x D R)),
        ((nb095_alpha_dummy_633 D R S_cls E), (nb095_alpha_dummy_635 x D R)),
        ((nb095_alpha_dummy_634 D R S_cls E), (nb095_alpha_dummy_636 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_631 D R S_cls E), (nb095_alpha_dummy_632 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_640
        D R S_cls E) ≠ (nb095_alpha_dummy_651 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_651
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641
        D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641
        D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_633 D R S_cls E) ≠
                                        (nb095_alpha_dummy_637 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_635 x D R) ≠
                                        (nb095_alpha_dummy_638 x D R) from (by
                                        unfold nb095_alpha_dummy_638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_637 D R S_cls E),
                                      (nb095_alpha_dummy_638 x D R)),
                                    ((nb095_alpha_dummy_633 D R S_cls E),
                                      (nb095_alpha_dummy_635 x D R)),
                                    ((nb095_alpha_dummy_634 D R S_cls E),
                                      (nb095_alpha_dummy_636 x D R)),
                                    ((nb095_alpha_dummy_626 D R S_cls E),
                                      (nb095_alpha_dummy_628 x D R)),
                                    ((nb095_alpha_dummy_625 D R S_cls E),
                                      (nb095_alpha_dummy_627 x D R)),
                                    ((nb095_alpha_dummy_631 D R S_cls E),
                                      (nb095_alpha_dummy_632 x D R)),
                                    ((nb095_alpha_dummy_629 D R S_cls E),
                                      (nb095_alpha_dummy_630 x D R)),
                                    ((nb095_alpha_dummy_620 D R S_cls E),
                                      (nb095_alpha_dummy_622 x D R)),
                                    ((nb095_alpha_dummy_619 D R S_cls E),
                                      (nb095_alpha_dummy_621 x D R)),
                                    ((nb095_alpha_dummy_623 D R S_cls E),
                                      (nb095_alpha_dummy_624 x D R)),
                                    ((nb095_alpha_dummy_617 D R S_cls E),
                                      (nb095_alpha_dummy_618 x D R)),
                                    ((nb095_alpha_dummy_615 D R S_cls E),
                                      (nb095_alpha_dummy_616 x D R)),
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
                                    (nb095_alpha_dummy_633 D R S_cls E) ≠
                                      (nb095_alpha_dummy_637 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_637;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_635 x D R) ≠
                                      (nb095_alpha_dummy_638 x D R) from (by
                                      unfold nb095_alpha_dummy_638;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0653 x D R) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_633 D R S_cls E) ≠
                                        (nb095_alpha_dummy_637 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_635 x D R) ≠
                                        (nb095_alpha_dummy_638 x D R) from (by
                                        unfold nb095_alpha_dummy_638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_637 D R S_cls E),
                                      (nb095_alpha_dummy_638 x D R)),
                                    ((nb095_alpha_dummy_633 D R S_cls E),
                                      (nb095_alpha_dummy_635 x D R)),
                                    ((nb095_alpha_dummy_634 D R S_cls E),
                                      (nb095_alpha_dummy_636 x D R)),
                                    ((nb095_alpha_dummy_626 D R S_cls E),
                                      (nb095_alpha_dummy_628 x D R)),
                                    ((nb095_alpha_dummy_625 D R S_cls E),
                                      (nb095_alpha_dummy_627 x D R)),
                                    ((nb095_alpha_dummy_631 D R S_cls E),
                                      (nb095_alpha_dummy_632 x D R)),
                                    ((nb095_alpha_dummy_629 D R S_cls E),
                                      (nb095_alpha_dummy_630 x D R)),
                                    ((nb095_alpha_dummy_620 D R S_cls E),
                                      (nb095_alpha_dummy_622 x D R)),
                                    ((nb095_alpha_dummy_619 D R S_cls E),
                                      (nb095_alpha_dummy_621 x D R)),
                                    ((nb095_alpha_dummy_623 D R S_cls E),
                                      (nb095_alpha_dummy_624 x D R)),
                                    ((nb095_alpha_dummy_617 D R S_cls E),
                                      (nb095_alpha_dummy_618 x D R)),
                                    ((nb095_alpha_dummy_615 D R S_cls E),
                                      (nb095_alpha_dummy_616 x D R)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                        (nb095_alpha_dummy_626 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_626;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_628 x D R) from (by
                        unfold nb095_alpha_dummy_628;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0646 x D R) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                          (nb095_alpha_dummy_625 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_625;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0644 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_627 x D R) from
                        (by
                          unfold nb095_alpha_dummy_627;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0646 x D R) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                            (nb095_alpha_dummy_631 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_631;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0648 D R S_cls E)
                                    0)))) (show
                          (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_632 x D R) from (by
                            unfold nb095_alpha_dummy_632;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0649 x D R) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_619 D R S_cls E) ≠
                              (nb095_alpha_dummy_629 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_629;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0645 D R S_cls E)
                                      0)))) (show
                            (nb095_alpha_dummy_621 x D R) ≠ (nb095_alpha_dummy_630 x D R) from
                            (by
                              unfold nb095_alpha_dummy_630;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0647 x D R) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪
                                ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                                        (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
                              (by decide)) (freshVar_injective (((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                      (syn_csn (Class.cv x))))).fv ∪ ((syn_cin D
                                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                                      (syn_csn (Class.cv x))))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_619 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_620 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_621 x D R))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_622 x D R))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_626 D R S_cls E) ≠
                                (nb095_alpha_dummy_633 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_633;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0650 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_635 x D R) from
                              (by
                                unfold nb095_alpha_dummy_635;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                        0)))) (TAlphaVar.there (show
                                (nb095_alpha_dummy_626 D R S_cls E) ≠
                                  (nb095_alpha_dummy_634 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_634;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0650 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_636 x D R)
                                from (by
                                  unfold nb095_alpha_dummy_636;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0651 x D R)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_628 x D R))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_633 D R S_cls E) ≠ (nb095_alpha_dummy_640 D R S_cls E) from (by
          unfold nb095_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_643 x D R) from
        (by
          unfold nb095_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_639 D R S_cls E) from (by
          unfold nb095_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_642 x D R) from
        (by
          unfold nb095_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_637 D R S_cls E) from (by
          unfold nb095_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
        (by
          unfold nb095_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D
                    R)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_641 D R S_cls E), (nb095_alpha_dummy_644 x D R)),
        ((nb095_alpha_dummy_640 D R S_cls E), (nb095_alpha_dummy_643 x D R)),
        ((nb095_alpha_dummy_639 D R S_cls E), (nb095_alpha_dummy_642 x D R)),
        ((nb095_alpha_dummy_637 D R S_cls E), (nb095_alpha_dummy_638 x D R)),
        ((nb095_alpha_dummy_633 D R S_cls E), (nb095_alpha_dummy_635 x D R)),
        ((nb095_alpha_dummy_634 D R S_cls E), (nb095_alpha_dummy_636 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_631 D R S_cls E), (nb095_alpha_dummy_632 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_640
        D R S_cls E) ≠ (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_641 D R S_cls E), (nb095_alpha_dummy_644 x D R)),
        ((nb095_alpha_dummy_640 D R S_cls E), (nb095_alpha_dummy_643 x D R)),
        ((nb095_alpha_dummy_639 D R S_cls E), (nb095_alpha_dummy_642 x D R)),
        ((nb095_alpha_dummy_637 D R S_cls E), (nb095_alpha_dummy_638 x D R)),
        ((nb095_alpha_dummy_633 D R S_cls E), (nb095_alpha_dummy_635 x D R)),
        ((nb095_alpha_dummy_634 D R S_cls E), (nb095_alpha_dummy_636 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_631 D R S_cls E), (nb095_alpha_dummy_632 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_640
        D R S_cls E) ≠ (nb095_alpha_dummy_651 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_651
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641
        D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641
        D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_637 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_637;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0652 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠
        (nb095_alpha_dummy_638 x D R) from (by
                                          unfold nb095_alpha_dummy_638;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0653 x D R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_637 D R S_cls E),
                                        (nb095_alpha_dummy_638 x D R)),
                                      ((nb095_alpha_dummy_633 D R S_cls E),
                                        (nb095_alpha_dummy_635 x D R)),
                                      ((nb095_alpha_dummy_634 D R S_cls E),
                                        (nb095_alpha_dummy_636 x D R)),
                                      ((nb095_alpha_dummy_626 D R S_cls E),
                                        (nb095_alpha_dummy_628 x D R)),
                                      ((nb095_alpha_dummy_625 D R S_cls E),
                                        (nb095_alpha_dummy_627 x D R)),
                                      ((nb095_alpha_dummy_631 D R S_cls E),
                                        (nb095_alpha_dummy_632 x D R)),
                                      ((nb095_alpha_dummy_629 D R S_cls E),
                                        (nb095_alpha_dummy_630 x D R)),
                                      ((nb095_alpha_dummy_620 D R S_cls E),
                                        (nb095_alpha_dummy_622 x D R)),
                                      ((nb095_alpha_dummy_619 D R S_cls E),
                                        (nb095_alpha_dummy_621 x D R)),
                                      ((nb095_alpha_dummy_623 D R S_cls E),
                                        (nb095_alpha_dummy_624 x D R)),
                                      ((nb095_alpha_dummy_617 D R S_cls E),
                                        (nb095_alpha_dummy_618 x D R)),
                                      ((nb095_alpha_dummy_615 D R S_cls E),
                                        (nb095_alpha_dummy_616 x D R)),
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
                                      (nb095_alpha_dummy_633 D R S_cls E) ≠
                                        (nb095_alpha_dummy_637 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_637;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_635 x D R) ≠
                                        (nb095_alpha_dummy_638 x D R) from (by
                                        unfold nb095_alpha_dummy_638;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0653 x D R) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_637 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_637;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0652 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠
        (nb095_alpha_dummy_638 x D R) from (by
                                          unfold nb095_alpha_dummy_638;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0653 x D R) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_637 D R S_cls E),
                                        (nb095_alpha_dummy_638 x D R)),
                                      ((nb095_alpha_dummy_633 D R S_cls E),
                                        (nb095_alpha_dummy_635 x D R)),
                                      ((nb095_alpha_dummy_634 D R S_cls E),
                                        (nb095_alpha_dummy_636 x D R)),
                                      ((nb095_alpha_dummy_626 D R S_cls E),
                                        (nb095_alpha_dummy_628 x D R)),
                                      ((nb095_alpha_dummy_625 D R S_cls E),
                                        (nb095_alpha_dummy_627 x D R)),
                                      ((nb095_alpha_dummy_631 D R S_cls E),
                                        (nb095_alpha_dummy_632 x D R)),
                                      ((nb095_alpha_dummy_629 D R S_cls E),
                                        (nb095_alpha_dummy_630 x D R)),
                                      ((nb095_alpha_dummy_620 D R S_cls E),
                                        (nb095_alpha_dummy_622 x D R)),
                                      ((nb095_alpha_dummy_619 D R S_cls E),
                                        (nb095_alpha_dummy_621 x D R)),
                                      ((nb095_alpha_dummy_623 D R S_cls E),
                                        (nb095_alpha_dummy_624 x D R)),
                                      ((nb095_alpha_dummy_617 D R S_cls E),
                                        (nb095_alpha_dummy_618 x D R)),
                                      ((nb095_alpha_dummy_615 D R S_cls E),
                                        (nb095_alpha_dummy_616 x D R)),
                                      ((nb095_alpha_dummy_004 D R S_cls E),
                                        (nb095_alpha_dummy_006 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_003 D R S_cls E),
                                        (nb095_alpha_dummy_005 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0086 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_659 D R S_cls E), (nb095_alpha_dummy_660 x D R)),
        ((nb095_alpha_dummy_657 D R S_cls E), (nb095_alpha_dummy_658 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_655 D R S_cls E), (nb095_alpha_dummy_656 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_659 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_659 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_626 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_660 x D R))
          (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_660 x D R))
            (syn_cphi (Class.cv (nb095_alpha_dummy_628 x D R)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                      (nb095_alpha_dummy_633 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_633;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_635 x D R) from (by
                      unfold nb095_alpha_dummy_635;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                        (nb095_alpha_dummy_634 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_634;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_636 x D R) from (by
                        unfold nb095_alpha_dummy_636;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0651 x D R) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                          (nb095_alpha_dummy_659 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_659;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0680 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_660 x D R) from
                        (by
                          unfold nb095_alpha_dummy_660;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0681 x D R) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                            (nb095_alpha_dummy_657 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_657;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0678 D R S_cls E)
                                    0)))) (show
                          (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_658 x D R) from (by
                            unfold nb095_alpha_dummy_658;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0679 x D R) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_628 x D R))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_633 D R S_cls E) ≠
                                        (nb095_alpha_dummy_640 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_640;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0654 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_635 x D R) ≠
                                        (nb095_alpha_dummy_643 x D R) from (by
                                        unfold nb095_alpha_dummy_643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0655 x D R) 1))))
                                    (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_639 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_639;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0654 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠
        (nb095_alpha_dummy_642 x D R) from (by
                                          unfold nb095_alpha_dummy_642;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0655 x D R) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_633 D R S_cls E) ≠ (nb095_alpha_dummy_637 D R S_cls E) from (by
          unfold nb095_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
        (by
          unfold nb095_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_641 D R S_cls E),
        (nb095_alpha_dummy_644 x D R)), ((nb095_alpha_dummy_640 D R S_cls E),
        (nb095_alpha_dummy_643 x D R)), ((nb095_alpha_dummy_639 D R S_cls E),
        (nb095_alpha_dummy_642 x D R)), ((nb095_alpha_dummy_637 D R S_cls E),
        (nb095_alpha_dummy_638 x D R)), ((nb095_alpha_dummy_633 D R S_cls E),
        (nb095_alpha_dummy_635 x D R)), ((nb095_alpha_dummy_634 D R S_cls E),
        (nb095_alpha_dummy_636 x D R)), ((nb095_alpha_dummy_659 D R S_cls E),
        (nb095_alpha_dummy_660 x D R)), ((nb095_alpha_dummy_657 D R S_cls E),
        (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_641 D R S_cls E),
        (nb095_alpha_dummy_644 x D R)), ((nb095_alpha_dummy_640 D R S_cls E),
        (nb095_alpha_dummy_643 x D R)), ((nb095_alpha_dummy_639 D R S_cls E),
        (nb095_alpha_dummy_642 x D R)), ((nb095_alpha_dummy_637 D R S_cls E),
        (nb095_alpha_dummy_638 x D R)), ((nb095_alpha_dummy_633 D R S_cls E),
        (nb095_alpha_dummy_635 x D R)), ((nb095_alpha_dummy_634 D R S_cls E),
        (nb095_alpha_dummy_636 x D R)), ((nb095_alpha_dummy_659 D R S_cls E),
        (nb095_alpha_dummy_660 x D R)), ((nb095_alpha_dummy_657 D R S_cls E),
        (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_633 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_651 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_651 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_633 D R S_cls E) ≠
                                (nb095_alpha_dummy_637 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
                              (by
                                unfold nb095_alpha_dummy_638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_637 D R S_cls E),
                              (nb095_alpha_dummy_638 x D R)),
                            ((nb095_alpha_dummy_633 D R S_cls E),
                              (nb095_alpha_dummy_635 x D R)),
                            ((nb095_alpha_dummy_634 D R S_cls E),
                              (nb095_alpha_dummy_636 x D R)),
                            ((nb095_alpha_dummy_659 D R S_cls E),
                              (nb095_alpha_dummy_660 x D R)),
                            ((nb095_alpha_dummy_657 D R S_cls E),
                              (nb095_alpha_dummy_658 x D R)),
                            ((nb095_alpha_dummy_626 D R S_cls E),
                              (nb095_alpha_dummy_628 x D R)),
                            ((nb095_alpha_dummy_625 D R S_cls E),
                              (nb095_alpha_dummy_627 x D R)),
                            ((nb095_alpha_dummy_655 D R S_cls E),
                              (nb095_alpha_dummy_656 x D R)),
                            ((nb095_alpha_dummy_629 D R S_cls E),
                              (nb095_alpha_dummy_630 x D R)),
                            ((nb095_alpha_dummy_620 D R S_cls E),
                              (nb095_alpha_dummy_622 x D R)),
                            ((nb095_alpha_dummy_619 D R S_cls E),
                              (nb095_alpha_dummy_621 x D R)),
                            ((nb095_alpha_dummy_623 D R S_cls E),
                              (nb095_alpha_dummy_624 x D R)),
                            ((nb095_alpha_dummy_617 D R S_cls E),
                              (nb095_alpha_dummy_618 x D R)),
                            ((nb095_alpha_dummy_615 D R S_cls E),
                              (nb095_alpha_dummy_616 x D R)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
                              (nb095_alpha_dummy_637 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_637;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0652 D R S_cls E)
                                      0)))) (show
                            (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
                            (by
                              unfold nb095_alpha_dummy_638;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0653 x D R) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_633 D R S_cls E) ≠
                                (nb095_alpha_dummy_637 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
                              (by
                                unfold nb095_alpha_dummy_638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_637 D R S_cls E),
                              (nb095_alpha_dummy_638 x D R)),
                            ((nb095_alpha_dummy_633 D R S_cls E),
                              (nb095_alpha_dummy_635 x D R)),
                            ((nb095_alpha_dummy_634 D R S_cls E),
                              (nb095_alpha_dummy_636 x D R)),
                            ((nb095_alpha_dummy_659 D R S_cls E),
                              (nb095_alpha_dummy_660 x D R)),
                            ((nb095_alpha_dummy_657 D R S_cls E),
                              (nb095_alpha_dummy_658 x D R)),
                            ((nb095_alpha_dummy_626 D R S_cls E),
                              (nb095_alpha_dummy_628 x D R)),
                            ((nb095_alpha_dummy_625 D R S_cls E),
                              (nb095_alpha_dummy_627 x D R)),
                            ((nb095_alpha_dummy_655 D R S_cls E),
                              (nb095_alpha_dummy_656 x D R)),
                            ((nb095_alpha_dummy_629 D R S_cls E),
                              (nb095_alpha_dummy_630 x D R)),
                            ((nb095_alpha_dummy_620 D R S_cls E),
                              (nb095_alpha_dummy_622 x D R)),
                            ((nb095_alpha_dummy_619 D R S_cls E),
                              (nb095_alpha_dummy_621 x D R)),
                            ((nb095_alpha_dummy_623 D R S_cls E),
                              (nb095_alpha_dummy_624 x D R)),
                            ((nb095_alpha_dummy_617 D R S_cls E),
                              (nb095_alpha_dummy_618 x D R)),
                            ((nb095_alpha_dummy_615 D R S_cls E),
                              (nb095_alpha_dummy_616 x D R)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                        (nb095_alpha_dummy_633 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_633;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_635 x D R) from (by
                        unfold nb095_alpha_dummy_635;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0651 x D R) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                          (nb095_alpha_dummy_634 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_634;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0650 D R S_cls E)
                                  1))))
                      (show (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_636 x D R) from
                        (by
                          unfold nb095_alpha_dummy_636;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0651 x D R) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                            (nb095_alpha_dummy_659 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_659;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0680 D R S_cls E)
                                    0)))) (show
                          (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_660 x D R) from (by
                            unfold nb095_alpha_dummy_660;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0681 x D R) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_626 D R S_cls E) ≠
                              (nb095_alpha_dummy_657 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_657;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0678 D R S_cls E)
                                      0)))) (show
                            (nb095_alpha_dummy_628 x D R) ≠ (nb095_alpha_dummy_658 x D R) from
                            (by
                              unfold nb095_alpha_dummy_658;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0679 x D R) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_626 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_628 x D R))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_633 D R S_cls E) ≠
        (nb095_alpha_dummy_640 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_640;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0654 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_635 x D R) ≠
        (nb095_alpha_dummy_643 x D R) from (by
                                          unfold nb095_alpha_dummy_643;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0655 x D R) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_633 D R S_cls E) ≠ (nb095_alpha_dummy_639 D R S_cls E) from (by
          unfold nb095_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0654 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_642 x D R) from
        (by
          unfold nb095_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0655 x D R) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_633 D R S_cls E) ≠ (nb095_alpha_dummy_637 D R S_cls E) from (by
          unfold nb095_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0652 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
        (by
          unfold nb095_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0653 x D R) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_641 D R S_cls E),
        (nb095_alpha_dummy_644 x D R)), ((nb095_alpha_dummy_640 D R S_cls E),
        (nb095_alpha_dummy_643 x D R)), ((nb095_alpha_dummy_639 D R S_cls E),
        (nb095_alpha_dummy_642 x D R)), ((nb095_alpha_dummy_637 D R S_cls E),
        (nb095_alpha_dummy_638 x D R)), ((nb095_alpha_dummy_633 D R S_cls E),
        (nb095_alpha_dummy_635 x D R)), ((nb095_alpha_dummy_634 D R S_cls E),
        (nb095_alpha_dummy_636 x D R)), ((nb095_alpha_dummy_659 D R S_cls E),
        (nb095_alpha_dummy_660 x D R)), ((nb095_alpha_dummy_657 D R S_cls E),
        (nb095_alpha_dummy_658 x D R)), ((nb095_alpha_dummy_626 D R S_cls E),
        (nb095_alpha_dummy_628 x D R)), ((nb095_alpha_dummy_625 D R S_cls E),
        (nb095_alpha_dummy_627 x D R)), ((nb095_alpha_dummy_655 D R S_cls E),
        (nb095_alpha_dummy_656 x D R)), ((nb095_alpha_dummy_629 D R S_cls E),
        (nb095_alpha_dummy_630 x D R)), ((nb095_alpha_dummy_620 D R S_cls E),
        (nb095_alpha_dummy_622 x D R)), ((nb095_alpha_dummy_619 D R S_cls E),
        (nb095_alpha_dummy_621 x D R)), ((nb095_alpha_dummy_623 D R S_cls E),
        (nb095_alpha_dummy_624 x D R)), ((nb095_alpha_dummy_617 D R S_cls E),
        (nb095_alpha_dummy_618 x D R)), ((nb095_alpha_dummy_615 D R S_cls E),
        (nb095_alpha_dummy_616 x D R)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0658
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0659
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0656
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0657
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_647 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_647;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0662
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_648 x D R) from
        (by
          unfold
            nb095_alpha_dummy_648;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0663
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_645 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_645;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0660
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_646 x D R) from
        (by
          unfold
            nb095_alpha_dummy_646;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0661
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_641 D R S_cls E), (nb095_alpha_dummy_644 x D R)),
        ((nb095_alpha_dummy_640 D R S_cls E), (nb095_alpha_dummy_643 x D R)),
        ((nb095_alpha_dummy_639 D R S_cls E), (nb095_alpha_dummy_642 x D R)),
        ((nb095_alpha_dummy_637 D R S_cls E), (nb095_alpha_dummy_638 x D R)),
        ((nb095_alpha_dummy_633 D R S_cls E), (nb095_alpha_dummy_635 x D R)),
        ((nb095_alpha_dummy_634 D R S_cls E), (nb095_alpha_dummy_636 x D R)),
        ((nb095_alpha_dummy_659 D R S_cls E), (nb095_alpha_dummy_660 x D R)),
        ((nb095_alpha_dummy_657 D R S_cls E), (nb095_alpha_dummy_658 x D R)),
        ((nb095_alpha_dummy_626 D R S_cls E), (nb095_alpha_dummy_628 x D R)),
        ((nb095_alpha_dummy_625 D R S_cls E), (nb095_alpha_dummy_627 x D R)),
        ((nb095_alpha_dummy_655 D R S_cls E), (nb095_alpha_dummy_656 x D R)),
        ((nb095_alpha_dummy_629 D R S_cls E), (nb095_alpha_dummy_630 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_633 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_651 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠ (nb095_alpha_dummy_651 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_651;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0666
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_652 x D R) from
        (by
          unfold
            nb095_alpha_dummy_652;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0667
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_640 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0664
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_643 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0665
                    x D R)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_633
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_635 x D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_641 D R S_cls E) ≠ (nb095_alpha_dummy_653 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_653;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0670
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_654 x D R) from
        (by
          unfold
            nb095_alpha_dummy_654;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0671
                    x D R)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_641 D R S_cls E) ≠
        (nb095_alpha_dummy_649 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_649;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0668
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_644 x D R) ≠ (nb095_alpha_dummy_650 x D R) from
        (by
          unfold
            nb095_alpha_dummy_650;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0669
                    x D R)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_633 D R S_cls E) ≠
                                  (nb095_alpha_dummy_637 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_637;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R)
                                from (by
                                  unfold nb095_alpha_dummy_638;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_637 D R S_cls E),
                                (nb095_alpha_dummy_638 x D R)),
                              ((nb095_alpha_dummy_633 D R S_cls E),
                                (nb095_alpha_dummy_635 x D R)),
                              ((nb095_alpha_dummy_634 D R S_cls E),
                                (nb095_alpha_dummy_636 x D R)),
                              ((nb095_alpha_dummy_659 D R S_cls E),
                                (nb095_alpha_dummy_660 x D R)),
                              ((nb095_alpha_dummy_657 D R S_cls E),
                                (nb095_alpha_dummy_658 x D R)),
                              ((nb095_alpha_dummy_626 D R S_cls E),
                                (nb095_alpha_dummy_628 x D R)),
                              ((nb095_alpha_dummy_625 D R S_cls E),
                                (nb095_alpha_dummy_627 x D R)),
                              ((nb095_alpha_dummy_655 D R S_cls E),
                                (nb095_alpha_dummy_656 x D R)),
                              ((nb095_alpha_dummy_629 D R S_cls E),
                                (nb095_alpha_dummy_630 x D R)),
                              ((nb095_alpha_dummy_620 D R S_cls E),
                                (nb095_alpha_dummy_622 x D R)),
                              ((nb095_alpha_dummy_619 D R S_cls E),
                                (nb095_alpha_dummy_621 x D R)),
                              ((nb095_alpha_dummy_623 D R S_cls E),
                                (nb095_alpha_dummy_624 x D R)),
                              ((nb095_alpha_dummy_617 D R S_cls E),
                                (nb095_alpha_dummy_618 x D R)),
                              ((nb095_alpha_dummy_615 D R S_cls E),
                                (nb095_alpha_dummy_616 x D R)),
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
                              (nb095_alpha_dummy_633 D R S_cls E) ≠
                                (nb095_alpha_dummy_637 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_637;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R) from
                              (by
                                unfold nb095_alpha_dummy_638;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_633 D R S_cls E) ≠
                                  (nb095_alpha_dummy_637 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_637;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0652 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_635 x D R) ≠ (nb095_alpha_dummy_638 x D R)
                                from (by
                                  unfold nb095_alpha_dummy_638;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0653 x D R)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_637 D R S_cls E),
                                (nb095_alpha_dummy_638 x D R)),
                              ((nb095_alpha_dummy_633 D R S_cls E),
                                (nb095_alpha_dummy_635 x D R)),
                              ((nb095_alpha_dummy_634 D R S_cls E),
                                (nb095_alpha_dummy_636 x D R)),
                              ((nb095_alpha_dummy_659 D R S_cls E),
                                (nb095_alpha_dummy_660 x D R)),
                              ((nb095_alpha_dummy_657 D R S_cls E),
                                (nb095_alpha_dummy_658 x D R)),
                              ((nb095_alpha_dummy_626 D R S_cls E),
                                (nb095_alpha_dummy_628 x D R)),
                              ((nb095_alpha_dummy_625 D R S_cls E),
                                (nb095_alpha_dummy_627 x D R)),
                              ((nb095_alpha_dummy_655 D R S_cls E),
                                (nb095_alpha_dummy_656 x D R)),
                              ((nb095_alpha_dummy_629 D R S_cls E),
                                (nb095_alpha_dummy_630 x D R)),
                              ((nb095_alpha_dummy_620 D R S_cls E),
                                (nb095_alpha_dummy_622 x D R)),
                              ((nb095_alpha_dummy_619 D R S_cls E),
                                (nb095_alpha_dummy_621 x D R)),
                              ((nb095_alpha_dummy_623 D R S_cls E),
                                (nb095_alpha_dummy_624 x D R)),
                              ((nb095_alpha_dummy_617 D R S_cls E),
                                (nb095_alpha_dummy_618 x D R)),
                              ((nb095_alpha_dummy_615 D R S_cls E),
                                (nb095_alpha_dummy_616 x D R)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb095_focused_notmem_0056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_620 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0057 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_622 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0058 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_619 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0059 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_621 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_623 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_619 D R S_cls E)} : Finset Var) ∪
            ({(nb095_alpha_dummy_620 D R S_cls E)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_620 D R S_cls E)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_619 D R S_cls E))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0061 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_624 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_621 x D R)} : Finset Var) ∪
            ({(nb095_alpha_dummy_622 x D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_621 x D R))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_622 x D R))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_621 x D R))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0062 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_617 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0063 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_618 x D R) ∉ D.fv :=
  by
  change
    freshVar
        ((R).fv ∪ ((syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_615 D R S_cls E) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
          ((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_focused_notmem_0065 (x : Var) (D : Class) (R : Class) :
    (nb095_alpha_dummy_616 x D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin R (syn_cxp (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv x))))))).fv ∪ ((syn_cnin R (syn_cxp (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (Class.cv x))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin R
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cxp
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x)))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_compact_envfresh_0298 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_247 D R S_cls E), (nb095_alpha_dummy_248 x D R)),
        ((nb095_alpha_dummy_245 D R S_cls E), (nb095_alpha_dummy_246 x D R)),
        ((nb095_alpha_dummy_620 D R S_cls E), (nb095_alpha_dummy_622 x D R)),
        ((nb095_alpha_dummy_619 D R S_cls E), (nb095_alpha_dummy_621 x D R)),
        ((nb095_alpha_dummy_623 D R S_cls E), (nb095_alpha_dummy_624 x D R)),
        ((nb095_alpha_dummy_617 D R S_cls E), (nb095_alpha_dummy_618 x D R)),
        ((nb095_alpha_dummy_615 D R S_cls E), (nb095_alpha_dummy_616 x D R)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_247 D R S_cls E) (nb095_alpha_dummy_248 x D R)
      (nb095_focused_notmem_0005 D R S_cls E) (nb095_focused_notmem_0006 x D R)
      (TEnvFresh.consFresh (nb095_alpha_dummy_245 D R S_cls E)
        (nb095_alpha_dummy_246 x D R) (nb095_focused_notmem_0007 D R S_cls E)
        (nb095_focused_notmem_0008 x D R)
        (TEnvFresh.consFresh (nb095_alpha_dummy_620 D R S_cls E)
          (nb095_alpha_dummy_622 x D R) (nb095_focused_notmem_0056 D R S_cls E)
          (nb095_focused_notmem_0057 x D R)
          (TEnvFresh.consFresh (nb095_alpha_dummy_619 D R S_cls E)
            (nb095_alpha_dummy_621 x D R) (nb095_focused_notmem_0058 D R S_cls E)
            (nb095_focused_notmem_0059 x D R)
            (TEnvFresh.consFresh (nb095_alpha_dummy_623 D R S_cls E)
              (nb095_alpha_dummy_624 x D R) (nb095_focused_notmem_0060 D R S_cls E)
              (nb095_focused_notmem_0061 x D R)
              (TEnvFresh.consFresh (nb095_alpha_dummy_617 D R S_cls E)
                (nb095_alpha_dummy_618 x D R) (nb095_focused_notmem_0062 D R S_cls E)
                (nb095_focused_notmem_0063 x D R)
                (TEnvFresh.consFresh (nb095_alpha_dummy_615 D R S_cls E)
                  (nb095_alpha_dummy_616 x D R) (nb095_focused_notmem_0064 D R S_cls E)
                  (nb095_focused_notmem_0065 x D R)
                  (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
                    (nb095_alpha_dummy_006 x u D R S_cls f E)
                    (nb095_focused_notmem_0048 D R S_cls E)
                    (nb095_focused_notmem_0049 x u D R S_cls f E)
                    (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
                      (nb095_alpha_dummy_005 x u D R S_cls f E)
                      (nb095_focused_notmem_0044 D R S_cls E)
                      (nb095_focused_notmem_0045 x u D R S_cls f E)
                      (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
                        (nb095_focused_notmem_0009 D R S_cls E) dv_D_u
                        (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                          (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
                          (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                            (nb095_focused_notmem_0001 D R S_cls E) dv_D_f
                            (TEnvFresh.nil D.fv)))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
