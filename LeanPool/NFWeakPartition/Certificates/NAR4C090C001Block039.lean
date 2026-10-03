/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block038

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part108`. -/


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
noncomputable def nb090_split_alpha_0086 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
        ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_667 A))
          (Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_667 A))
            (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_668 u))
          (Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_668 u))
            (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_662 A) from (by
                      unfold nb090_alpha_dummy_662;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
                  (show u ≠ (nb090_alpha_dummy_664 u) from (by
                      unfold nb090_alpha_dummy_664;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_661 A) from (by
                        unfold nb090_alpha_dummy_661;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
                    (show u ≠ (nb090_alpha_dummy_663 u) from (by
                        unfold nb090_alpha_dummy_663;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0690 u) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_667 A) from (by
                          unfold nb090_alpha_dummy_667;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0692 A) 0))))
                      (show u ≠ (nb090_alpha_dummy_668 u) from (by
                          unfold nb090_alpha_dummy_668;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0693 u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_665 A) from (by
                            unfold nb090_alpha_dummy_665;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0689 A) 0))))
                        (show u ≠ (nb090_alpha_dummy_666 u) from (by
                            unfold nb090_alpha_dummy_666;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0691 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_653 A) from (by
                              unfold nb090_alpha_dummy_653;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
                          (show u ≠ (nb090_alpha_dummy_654 u) from (by
                              unfold nb090_alpha_dummy_654;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0685 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_655 A) from (by
                                unfold nb090_alpha_dummy_655;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
                            (show u ≠ (nb090_alpha_dummy_656 u) from (by
                                unfold nb090_alpha_dummy_656;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_658 A) from
                                (by
                                  unfold nb090_alpha_dummy_658;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0684 A) 1))))
                              (show u ≠ (nb090_alpha_dummy_660 u) from (by
                                  unfold nb090_alpha_dummy_660;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0687 u) 1))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_657 A) from (by
                                    unfold nb090_alpha_dummy_657;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0684 A)
                                            0)))) (show u ≠ (nb090_alpha_dummy_659 u) from (by
                                    unfold nb090_alpha_dummy_659;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0687 u)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_042 A) from
                                    (by
                                      unfold nb090_alpha_dummy_042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0642 A)
                                              1)))) (show u ≠ (nb090_alpha_dummy_044 v u h) from
                                    (by
                                      unfold nb090_alpha_dummy_044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0643 v u h) 1))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
                                        (nb090_alpha_dummy_041 A) from (by
                                        unfold nb090_alpha_dummy_041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                0))))
                                    (show u ≠ (nb090_alpha_dummy_043 v u h) from (by
                                        unfold nb090_alpha_dummy_043;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0643 v u h) 0))))
                                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                      (Ne.symm dv_h_u) (TAlphaVar.there
                                        (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                        (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_669 A) from (by
                              unfold nb090_alpha_dummy_669;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                          (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_671 u) from (by
                              unfold nb090_alpha_dummy_671;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_670 A) from (by
                                unfold nb090_alpha_dummy_670;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                            (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_672 u) from (by
                                unfold nb090_alpha_dummy_672;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_676 A) from (by
          unfold nb090_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 1)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_679 u) from (by
          unfold nb090_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_675 A) from (by
          unfold nb090_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 0)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_678 u) from (by
          unfold nb090_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
          unfold nb090_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A)
                  0)))) (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
          unfold nb090_alpha_dummy_674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A),
        (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A),
        (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A),
        (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A),
        (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A),
        (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_676
        A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A),
        (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A),
        (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A),
        (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A),
        (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A),
        (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671
        u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677
        A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677
        A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                      (by
                                        unfold nb090_alpha_dummy_673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090_alpha_dummy_671 u) ≠
                                        (nb090_alpha_dummy_674 u) from (by
                                        unfold nb090_alpha_dummy_674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                                    ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                                    ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                                    ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                                    ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                                    ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
                                    ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                                    ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                                    ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                                    ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                                    ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                    (by
                                      unfold nb090_alpha_dummy_673;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0696 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from
                                    (by
                                      unfold nb090_alpha_dummy_674;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0697 u)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                      (by
                                        unfold nb090_alpha_dummy_673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090_alpha_dummy_671 u) ≠
                                        (nb090_alpha_dummy_674 u) from (by
                                        unfold nb090_alpha_dummy_674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                                    ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                                    ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                                    ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                                    ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                                    ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
                                    ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                                    ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                                    ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                                    ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                                    ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_662 A) from (by
                        unfold nb090_alpha_dummy_662;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
                    (show u ≠ (nb090_alpha_dummy_664 u) from (by
                        unfold nb090_alpha_dummy_664;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0690 u) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_661 A) from (by
                          unfold nb090_alpha_dummy_661;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
                      (show u ≠ (nb090_alpha_dummy_663 u) from (by
                          unfold nb090_alpha_dummy_663;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_667 A) from (by
                            unfold nb090_alpha_dummy_667;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0692 A) 0))))
                        (show u ≠ (nb090_alpha_dummy_668 u) from (by
                            unfold nb090_alpha_dummy_668;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0693 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_665 A) from (by
                              unfold nb090_alpha_dummy_665;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0689 A) 0))))
                          (show u ≠ (nb090_alpha_dummy_666 u) from (by
                              unfold nb090_alpha_dummy_666;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0691 u) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_653 A) from (by
                                unfold nb090_alpha_dummy_653;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
                            (show u ≠ (nb090_alpha_dummy_654 u) from (by
                                unfold nb090_alpha_dummy_654;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0685 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_655 A) from
                                (by
                                  unfold nb090_alpha_dummy_655;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
                              (show u ≠ (nb090_alpha_dummy_656 u) from (by
                                  unfold nb090_alpha_dummy_656;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_658 A) from (by
                                    unfold nb090_alpha_dummy_658;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0684 A)
                                            1)))) (show u ≠ (nb090_alpha_dummy_660 u) from (by
                                    unfold nb090_alpha_dummy_660;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0687 u)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_657 A) from
                                    (by
                                      unfold nb090_alpha_dummy_657;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0684 A)
                                              0)))) (show u ≠ (nb090_alpha_dummy_659 u) from (by
                                      unfold nb090_alpha_dummy_659;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0687 u)
                                              0)))) (TAlphaVar.there (show
                                      (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_042 A) from
                                      (by
                                        unfold nb090_alpha_dummy_042;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                1))))
                                    (show u ≠ (nb090_alpha_dummy_044 v u h) from (by
                                        unfold nb090_alpha_dummy_044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0643 v u h) 1))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_001 A) ≠
        (nb090_alpha_dummy_041 A) from (by
                                          unfold nb090_alpha_dummy_041;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0642 A) 0))))
                                      (show u ≠ (nb090_alpha_dummy_043 v u h) from (by
                                          unfold nb090_alpha_dummy_043;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0643 v u h) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_h_u) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _)))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_653 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_669 A) from (by
                                unfold nb090_alpha_dummy_669;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                            (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_671 u) from (by
                                unfold nb090_alpha_dummy_671;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_670 A) from
                                (by
                                  unfold nb090_alpha_dummy_670;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                              (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_672 u) from
                                (by
                                  unfold nb090_alpha_dummy_672;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_662 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_664 u))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_676 A) from (by
          unfold nb090_alpha_dummy_676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 1)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_679 u) from (by
          unfold nb090_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_675 A) from (by
          unfold nb090_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A)
                  0)))) (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_678 u) from (by
          unfold nb090_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_669 A) ≠
        (nb090_alpha_dummy_673 A) from (by
          unfold nb090_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A)
                  0)))) (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
          unfold nb090_alpha_dummy_674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A),
        (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A),
        (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A),
        (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A),
        (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A),
        (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_676
        A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A),
        (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A),
        (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A),
        (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A),
        (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A),
        (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_671
        u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677
        A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677
        A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A)
                                        from (by
                                          unfold nb090_alpha_dummy_673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0696 A) 0)))) (show
                                        (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u)
                                        from (by
                                          unfold nb090_alpha_dummy_674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0697 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                                      ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                                      ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                                      ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                                      ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                                      ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
                                      ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                                      ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                                      ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                                      ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                                      ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                      (by
                                        unfold nb090_alpha_dummy_673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090_alpha_dummy_671 u) ≠
                                        (nb090_alpha_dummy_674 u) from (by
                                        unfold nb090_alpha_dummy_674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A)
                                        from (by
                                          unfold nb090_alpha_dummy_673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0696 A) 0)))) (show
                                        (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u)
                                        from (by
                                          unfold nb090_alpha_dummy_674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0697 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                                      ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                                      ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                                      ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                                      ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                                      ((nb090_alpha_dummy_667 A), (nb090_alpha_dummy_668 u)),
                                      ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                                      ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                                      ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                                      ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                                      ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                                      ((nb090_alpha_dummy_042 A),
                                        (nb090_alpha_dummy_044 v u h)),
                                      ((nb090_alpha_dummy_041 A),
                                        (nb090_alpha_dummy_043 v u h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part109`. -/


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
noncomputable def nb090_split_alpha_0087 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
        ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
        ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
        ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_695 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_695 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_696 u))
          (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_696 u))
            (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_669 A) from (by
                      unfold nb090_alpha_dummy_669;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                  (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_671 u) from (by
                      unfold nb090_alpha_dummy_671;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_670 A) from (by
                        unfold nb090_alpha_dummy_670;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                    (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_672 u) from (by
                        unfold nb090_alpha_dummy_672;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0695 u) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_695 A) from (by
                          unfold nb090_alpha_dummy_695;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0724 A) 0))))
                      (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_696 u) from (by
                          unfold nb090_alpha_dummy_696;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0725 u) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_693 A) from (by
                            unfold nb090_alpha_dummy_693;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0722 A) 0))))
                        (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_694 u) from (by
                            unfold nb090_alpha_dummy_694;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0723 u) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_676 A) from
                                      (by
                                        unfold nb090_alpha_dummy_676;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0698 A)
                                                1)))) (show (nb090_alpha_dummy_671 u) ≠
                                        (nb090_alpha_dummy_679 u) from (by
                                        unfold nb090_alpha_dummy_679;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0699 u)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_675 A)
                                        from (by
                                          unfold nb090_alpha_dummy_675;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0698 A) 0)))) (show
                                        (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_678 u)
                                        from (by
                                          unfold nb090_alpha_dummy_678;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0699 u) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_669 A) ≠
        (nb090_alpha_dummy_673 A) from (by
          unfold nb090_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A) 0)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_674 u) from (by
          unfold nb090_alpha_dummy_674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_677 A),
        (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)),
                                        ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
                                        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                                        ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                                        ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                                        ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
                                        ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
                                        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                                        ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                                        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
                                        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                                        ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                                        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                                        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                                        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                                        ((nb090_alpha_dummy_042 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)),
        ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A),
        (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
        ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A),
        (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
        ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A),
        (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
        ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A),
        (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A),
        (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
                                unfold nb090_alpha_dummy_673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
                                unfold nb090_alpha_dummy_674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                            ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                            ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                            ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
                            ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
                            ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                            ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                            ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
                            ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                            ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                            ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                            ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                            ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
                              unfold nb090_alpha_dummy_673;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                          (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
                              unfold nb090_alpha_dummy_674;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
                                unfold nb090_alpha_dummy_673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
                                unfold nb090_alpha_dummy_674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                            ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                            ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                            ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
                            ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
                            ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                            ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                            ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
                            ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                            ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                            ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                            ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                            ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_669 A) from (by
                        unfold nb090_alpha_dummy_669;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                    (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_671 u) from (by
                        unfold nb090_alpha_dummy_671;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0695 u) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_670 A) from (by
                          unfold nb090_alpha_dummy_670;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                      (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_672 u) from (by
                          unfold nb090_alpha_dummy_672;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_695 A) from (by
                            unfold nb090_alpha_dummy_695;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0724 A) 0))))
                        (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_696 u) from (by
                            unfold nb090_alpha_dummy_696;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0725 u) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_662 A) ≠ (nb090_alpha_dummy_693 A) from (by
                              unfold nb090_alpha_dummy_693;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0722 A) 0))))
                          (show (nb090_alpha_dummy_664 u) ≠ (nb090_alpha_dummy_694 u) from (by
                              unfold nb090_alpha_dummy_694;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0723 u) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_662 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_664 u))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_669 A) ≠
        (nb090_alpha_dummy_676 A) from (by
                                          unfold nb090_alpha_dummy_676;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0698 A) 1)))) (show
                                        (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_679 u)
                                        from (by
                                          unfold nb090_alpha_dummy_679;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0699 u) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_669 A) ≠
        (nb090_alpha_dummy_675 A) from (by
          unfold nb090_alpha_dummy_675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 0)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_678 u) from (by
          unfold nb090_alpha_dummy_678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
          unfold nb090_alpha_dummy_673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A) 0)))) (show (nb090_alpha_dummy_671 u) ≠
        (nb090_alpha_dummy_674 u) from (by
          unfold nb090_alpha_dummy_674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_677 A),
        (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A), (nb090_alpha_dummy_679 u)),
        ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)), ((nb090_alpha_dummy_673 A),
        (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
        ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)), ((nb090_alpha_dummy_695 A),
        (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
        ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)), ((nb090_alpha_dummy_661 A),
        (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
        ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)), ((nb090_alpha_dummy_653 A),
        (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)), ((nb090_alpha_dummy_657 A),
        (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_683 A) from (by
          unfold
            nb090_alpha_dummy_683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_684 u) from (by
          unfold
            nb090_alpha_dummy_684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_681 A) from (by
          unfold
            nb090_alpha_dummy_681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_682 u) from (by
          unfold
            nb090_alpha_dummy_682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_677 A), (nb090_alpha_dummy_680 u)), ((nb090_alpha_dummy_676 A),
        (nb090_alpha_dummy_679 u)), ((nb090_alpha_dummy_675 A), (nb090_alpha_dummy_678 u)),
        ((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)), ((nb090_alpha_dummy_669 A),
        (nb090_alpha_dummy_671 u)), ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
        ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)), ((nb090_alpha_dummy_693 A),
        (nb090_alpha_dummy_694 u)), ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
        ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)), ((nb090_alpha_dummy_691 A),
        (nb090_alpha_dummy_692 u)), ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
        ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)), ((nb090_alpha_dummy_655 A),
        (nb090_alpha_dummy_656 u)), ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠ (nb090_alpha_dummy_687 A) from (by
          unfold
            nb090_alpha_dummy_687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_688 u) from (by
          unfold
            nb090_alpha_dummy_688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_676 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090_alpha_dummy_679 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_669
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_677 A) ≠ (nb090_alpha_dummy_689 A) from (by
          unfold
            nb090_alpha_dummy_689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_690 u) from (by
          unfold
            nb090_alpha_dummy_690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_677 A) ≠
        (nb090_alpha_dummy_685 A) from (by
          unfold
            nb090_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090_alpha_dummy_680 u) ≠ (nb090_alpha_dummy_686 u) from (by
          unfold
            nb090_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                (by
                                  unfold nb090_alpha_dummy_673;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                              (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from
                                (by
                                  unfold nb090_alpha_dummy_674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                              ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                              ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                              ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
                              ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
                              ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                              ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                              ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
                              ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                              ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                              ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                              ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                              ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from (by
                                unfold nb090_alpha_dummy_673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from (by
                                unfold nb090_alpha_dummy_674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_669 A) ≠ (nb090_alpha_dummy_673 A) from
                                (by
                                  unfold nb090_alpha_dummy_673;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                              (show (nb090_alpha_dummy_671 u) ≠ (nb090_alpha_dummy_674 u) from
                                (by
                                  unfold nb090_alpha_dummy_674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_673 A), (nb090_alpha_dummy_674 u)),
                              ((nb090_alpha_dummy_669 A), (nb090_alpha_dummy_671 u)),
                              ((nb090_alpha_dummy_670 A), (nb090_alpha_dummy_672 u)),
                              ((nb090_alpha_dummy_695 A), (nb090_alpha_dummy_696 u)),
                              ((nb090_alpha_dummy_693 A), (nb090_alpha_dummy_694 u)),
                              ((nb090_alpha_dummy_662 A), (nb090_alpha_dummy_664 u)),
                              ((nb090_alpha_dummy_661 A), (nb090_alpha_dummy_663 u)),
                              ((nb090_alpha_dummy_691 A), (nb090_alpha_dummy_692 u)),
                              ((nb090_alpha_dummy_665 A), (nb090_alpha_dummy_666 u)),
                              ((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
                              ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
                              ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
                              ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb090_wpp_notmem_1804 (A : Class) : (nb090_alpha_dummy_653 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_653, fv_syn_c1st] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1805 (u : Var) : (nb090_alpha_dummy_654 u) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_654, fv_syn_c1st] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1806 (A : Class) : (nb090_alpha_dummy_655 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_655, fv_syn_c1st] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1807 (u : Var) : (nb090_alpha_dummy_656 u) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_656, fv_syn_c1st] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1808 (A : Class) : (nb090_alpha_dummy_658 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_658, fv_syn_c1st] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1809 (u : Var) : (nb090_alpha_dummy_660 u) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_660, fv_syn_c1st] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1810 (A : Class) : (nb090_alpha_dummy_657 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_657, fv_syn_c1st] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1811 (u : Var) : (nb090_alpha_dummy_659 u) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_659, fv_syn_c1st] using (nb090_compact_fv_empty_0519 u)

theorem nb090_wpp_notmem_1812 (A : Class) : (nb090_alpha_dummy_042 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_042, fv_syn_c1st] using (nb090_compact_fv_empty_0464 A)

theorem nb090_wpp_notmem_1813 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_044, fv_syn_c1st] using
    (nb090_compact_fv_empty_0465 v u h)

theorem nb090_wpp_notmem_1814 (A : Class) : (nb090_alpha_dummy_041 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_041, fv_syn_c1st] using (nb090_compact_fv_empty_0462 A)

theorem nb090_wpp_notmem_1815 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_043, fv_syn_c1st] using
    (nb090_compact_fv_empty_0463 v u h)

theorem nb090_wpp_notmem_1816 (A : Class) : (nb090_alpha_dummy_000 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_000, fv_syn_c1st] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_1817 (h : Var) : h ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_1818 (A : Class) : (nb090_alpha_dummy_002 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_002, fv_syn_c1st] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_1819 (v : Var) : v ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_1820 (A : Class) : (nb090_alpha_dummy_001 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_001, fv_syn_c1st] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_1821 (u : Var) : u ∉ ((syn_c1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_1822 (A : Class) : (nb090_alpha_dummy_003 A) ∉ ((syn_c1st)).fv :=
  by simpa only [nb090_alpha_dummy_003, fv_syn_c1st] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_1823 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉ ((syn_c1st)).fv := by
  simpa only [nb090_alpha_dummy_004, fv_syn_c1st] using
    (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0298 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090_alpha_dummy_653 A) (nb090_alpha_dummy_654 u)
      (nb090_wpp_notmem_1804 A) (nb090_wpp_notmem_1805 u)
      (TEnvFresh.consFresh (nb090_alpha_dummy_655 A) (nb090_alpha_dummy_656 u)
        (nb090_wpp_notmem_1806 A) (nb090_wpp_notmem_1807 u)
        (TEnvFresh.consFresh (nb090_alpha_dummy_658 A) (nb090_alpha_dummy_660 u)
          (nb090_wpp_notmem_1808 A) (nb090_wpp_notmem_1809 u)
          (TEnvFresh.consFresh (nb090_alpha_dummy_657 A) (nb090_alpha_dummy_659 u)
            (nb090_wpp_notmem_1810 A) (nb090_wpp_notmem_1811 u)
            (TEnvFresh.consFresh (nb090_alpha_dummy_042 A) (nb090_alpha_dummy_044 v u h)
              (nb090_wpp_notmem_1812 A) (nb090_wpp_notmem_1813 v u h)
              (TEnvFresh.consFresh (nb090_alpha_dummy_041 A) (nb090_alpha_dummy_043 v u h)
                (nb090_wpp_notmem_1814 A) (nb090_wpp_notmem_1815 v u h)
                (TEnvFresh.consFresh (nb090_alpha_dummy_000 A) h (nb090_wpp_notmem_1816 A)
                  (nb090_wpp_notmem_1817 h) (TEnvFresh.consFresh (nb090_alpha_dummy_002 A) v
                    (nb090_wpp_notmem_1818 A) (nb090_wpp_notmem_1819 v)
                    (TEnvFresh.consFresh (nb090_alpha_dummy_001 A) u
                      (nb090_wpp_notmem_1820 A) (nb090_wpp_notmem_1821 u)
                      (TEnvFresh.consFresh (nb090_alpha_dummy_003 A)
                        (nb090_alpha_dummy_004 v u A h) (nb090_wpp_notmem_1822 A)
                        (nb090_wpp_notmem_1823 v u A h)
                        (TEnvFresh.nil ((syn_c1st)).fv)))))))))))

@[expose]
noncomputable def nb090_wpp_refl_0298 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090_alpha_dummy_653 A), (nb090_alpha_dummy_654 u)),
        ((nb090_alpha_dummy_655 A), (nb090_alpha_dummy_656 u)),
        ((nb090_alpha_dummy_658 A), (nb090_alpha_dummy_660 u)),
        ((nb090_alpha_dummy_657 A), (nb090_alpha_dummy_659 u)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      ((syn_c1st)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0298 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
