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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0086`. -/
@[expose]
noncomputable def nb090SplitAlpha0086 (v : Var) (u : Var) (A : Class) (h : Var)
    (dv_h_u : h ≠ u) (dv_u_v : u ≠ v) :
    TAlphaWff
      [((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
        ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy667 A))
          (Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy667 A))
            (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCphi (Class.cv (nb090AlphaDummy662 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy668 u))
          (Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy668 u))
            (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCphi (Class.cv (nb090AlphaDummy664 u))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy662 A) from (by
                      unfold nb090AlphaDummy662;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
                  (show u ≠ (nb090AlphaDummy664 u) from (by
                      unfold nb090AlphaDummy664;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy661 A) from (by
                        unfold nb090AlphaDummy661;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
                    (show u ≠ (nb090AlphaDummy663 u) from (by
                        unfold nb090AlphaDummy663;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0690 u) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy667 A) from (by
                          unfold nb090AlphaDummy667;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0692 A) 0))))
                      (show u ≠ (nb090AlphaDummy668 u) from (by
                          unfold nb090AlphaDummy668;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0693 u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy665 A) from (by
                            unfold nb090AlphaDummy665;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0689 A) 0))))
                        (show u ≠ (nb090AlphaDummy666 u) from (by
                            unfold nb090AlphaDummy666;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0691 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy653 A) from (by
                              unfold nb090AlphaDummy653;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
                          (show u ≠ (nb090AlphaDummy654 u) from (by
                              unfold nb090AlphaDummy654;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0685 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy655 A) from (by
                                unfold nb090AlphaDummy655;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
                            (show u ≠ (nb090AlphaDummy656 u) from (by
                                unfold nb090AlphaDummy656;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy658 A) from
                                (by
                                  unfold nb090AlphaDummy658;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0684 A) 1))))
                              (show u ≠ (nb090AlphaDummy660 u) from (by
                                  unfold nb090AlphaDummy660;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0687 u) 1))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy657 A) from (by
                                    unfold nb090AlphaDummy657;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0684 A)
                                            0)))) (show u ≠ (nb090AlphaDummy659 u) from (by
                                    unfold nb090AlphaDummy659;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0687 u)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy042 A) from
                                    (by
                                      unfold nb090AlphaDummy042;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0642 A)
                                              1)))) (show u ≠ (nb090AlphaDummy044 v u h) from
                                    (by
                                      unfold nb090AlphaDummy044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0643 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
                                        (nb090AlphaDummy041 A) from (by
                                        unfold nb090AlphaDummy041;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                0))))
                                    (show u ≠ (nb090AlphaDummy043 v u h) from (by
                                        unfold nb090AlphaDummy043;
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
                    (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy669 A) from (by
                              unfold nb090AlphaDummy669;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                          (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy671 u) from (by
                              unfold nb090AlphaDummy671;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy670 A) from (by
                                unfold nb090AlphaDummy670;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                            (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy672 u) from (by
                                unfold nb090AlphaDummy672;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy662 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy664 u))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy676 A) from (by
          unfold nb090AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 1)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy679 u) from (by
          unfold nb090AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy675 A) from (by
          unfold nb090AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 0)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy678 u) from (by
          unfold nb090AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
          unfold nb090AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A)
                  0)))) (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
          unfold nb090AlphaDummy674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A),
        (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A),
        (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A),
        (nb090AlphaDummy663 u)), ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A),
        (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A),
        (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy676
        A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A),
        (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A),
        (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A),
        (nb090AlphaDummy663 u)), ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A),
        (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A),
        (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy671
        u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677
        A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677
        A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                      (by
                                        unfold nb090AlphaDummy673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090AlphaDummy671 u) ≠
                                        (nb090AlphaDummy674 u) from (by
                                        unfold nb090AlphaDummy674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                                    ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                                    ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                                    ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                                    ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                                    ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
                                    ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                                    ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                                    ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                                    ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                                    ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                    (by
                                      unfold nb090AlphaDummy673;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0696 A)
                                              0)))) (show
                                    (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from
                                    (by
                                      unfold nb090AlphaDummy674;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0697 u)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                      (by
                                        unfold nb090AlphaDummy673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090AlphaDummy671 u) ≠
                                        (nb090AlphaDummy674 u) from (by
                                        unfold nb090AlphaDummy674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                                    ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                                    ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                                    ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                                    ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                                    ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
                                    ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                                    ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                                    ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                                    ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                                    ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy662 A) from (by
                        unfold nb090AlphaDummy662;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
                    (show u ≠ (nb090AlphaDummy664 u) from (by
                        unfold nb090AlphaDummy664;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0690 u) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy661 A) from (by
                          unfold nb090AlphaDummy661;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
                      (show u ≠ (nb090AlphaDummy663 u) from (by
                          unfold nb090AlphaDummy663;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy667 A) from (by
                            unfold nb090AlphaDummy667;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0692 A) 0))))
                        (show u ≠ (nb090AlphaDummy668 u) from (by
                            unfold nb090AlphaDummy668;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0693 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy665 A) from (by
                              unfold nb090AlphaDummy665;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0689 A) 0))))
                          (show u ≠ (nb090AlphaDummy666 u) from (by
                              unfold nb090AlphaDummy666;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0691 u) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy653 A) from (by
                                unfold nb090AlphaDummy653;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
                            (show u ≠ (nb090AlphaDummy654 u) from (by
                                unfold nb090AlphaDummy654;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0685 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy655 A) from
                                (by
                                  unfold nb090AlphaDummy655;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
                              (show u ≠ (nb090AlphaDummy656 u) from (by
                                  unfold nb090AlphaDummy656;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
                              (TAlphaVar.there (show
                                  (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy658 A) from (by
                                    unfold nb090AlphaDummy658;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0684 A)
                                            1)))) (show u ≠ (nb090AlphaDummy660 u) from (by
                                    unfold nb090AlphaDummy660;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0687 u)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy657 A) from
                                    (by
                                      unfold nb090AlphaDummy657;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0684 A)
                                              0)))) (show u ≠ (nb090AlphaDummy659 u) from (by
                                      unfold nb090AlphaDummy659;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0687 u)
                                              0)))) (TAlphaVar.there (show
                                      (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy042 A) from
                                      (by
                                        unfold nb090AlphaDummy042;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0642 A)
                                                1))))
                                    (show u ≠ (nb090AlphaDummy044 v u h) from (by
                                        unfold nb090AlphaDummy044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0643 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy001 A) ≠
        (nb090AlphaDummy041 A) from (by
                                          unfold nb090AlphaDummy041;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0642 A) 0))))
                                      (show u ≠ (nb090AlphaDummy043 v u h) from (by
                                          unfold nb090AlphaDummy043;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0643 v u h) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_h_u) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _)))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy001 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy653 A))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy669 A) from (by
                                unfold nb090AlphaDummy669;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                            (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy671 u) from (by
                                unfold nb090AlphaDummy671;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy670 A) from
                                (by
                                  unfold nb090AlphaDummy670;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                              (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy672 u) from
                                (by
                                  unfold nb090AlphaDummy672;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy662 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy664 u))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy676 A) from (by
          unfold nb090AlphaDummy676;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 1)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy679 u) from (by
          unfold nb090AlphaDummy679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy675 A) from (by
          unfold nb090AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A)
                  0)))) (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy678 u) from (by
          unfold nb090AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy669 A) ≠
        (nb090AlphaDummy673 A) from (by
          unfold nb090AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A)
                  0)))) (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
          unfold nb090AlphaDummy674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A),
        (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A),
        (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A),
        (nb090AlphaDummy663 u)), ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A),
        (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A),
        (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy676
        A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A),
        (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A),
        (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A),
        (nb090AlphaDummy663 u)), ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A),
        (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A),
        (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy671
        u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677
        A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677
        A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A)
                                        from (by
                                          unfold nb090AlphaDummy673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0696 A) 0)))) (show
                                        (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u)
                                        from (by
                                          unfold nb090AlphaDummy674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0697 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                                      ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                                      ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                                      ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                                      ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                                      ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
                                      ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                                      ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                                      ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                                      ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                                      ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                      (by
                                        unfold nb090AlphaDummy673;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0696 A)
                                                0)))) (show (nb090AlphaDummy671 u) ≠
                                        (nb090AlphaDummy674 u) from (by
                                        unfold nb090AlphaDummy674;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0697 u)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A)
                                        from (by
                                          unfold nb090AlphaDummy673;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0696 A) 0)))) (show
                                        (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u)
                                        from (by
                                          unfold nb090AlphaDummy674;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0697 u) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                                      ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                                      ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                                      ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                                      ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                                      ((nb090AlphaDummy667 A), (nb090AlphaDummy668 u)),
                                      ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                                      ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                                      ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                                      ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                                      ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                                      ((nb090AlphaDummy042 A),
                                        (nb090AlphaDummy044 v u h)),
                                      ((nb090AlphaDummy041 A),
                                        (nb090AlphaDummy043 v u h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0087`. -/
@[expose]
noncomputable def nb090SplitAlpha0087 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
        ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
        ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
        ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy695 A))
          (synCphi (Class.cv (nb090AlphaDummy662 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy695 A))
            (synCphi (Class.cv (nb090AlphaDummy662 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy696 u))
          (synCphi (Class.cv (nb090AlphaDummy664 u)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy696 u))
            (synCphi (Class.cv (nb090AlphaDummy664 u)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy669 A) from (by
                      unfold nb090AlphaDummy669;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                  (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy671 u) from (by
                      unfold nb090AlphaDummy671;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0695 u) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy670 A) from (by
                        unfold nb090AlphaDummy670;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                    (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy672 u) from (by
                        unfold nb090AlphaDummy672;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0695 u) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy695 A) from (by
                          unfold nb090AlphaDummy695;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0724 A) 0))))
                      (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy696 u) from (by
                          unfold nb090AlphaDummy696;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0725 u) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy693 A) from (by
                            unfold nb090AlphaDummy693;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0722 A) 0))))
                        (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy694 u) from (by
                            unfold nb090AlphaDummy694;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0723 u) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy662 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy664 u))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy676 A) from
                                      (by
                                        unfold nb090AlphaDummy676;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0698 A)
                                                1)))) (show (nb090AlphaDummy671 u) ≠
                                        (nb090AlphaDummy679 u) from (by
                                        unfold nb090AlphaDummy679;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0699 u)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy675 A)
                                        from (by
                                          unfold nb090AlphaDummy675;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0698 A) 0)))) (show
                                        (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy678 u)
                                        from (by
                                          unfold nb090AlphaDummy678;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0699 u) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy669 A) ≠
        (nb090AlphaDummy673 A) from (by
          unfold nb090AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A) 0)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy674 u) from (by
          unfold nb090AlphaDummy674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy677 A),
        (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A), (nb090AlphaDummy679 u)),
                                        ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
                                        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                                        ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                                        ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                                        ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
                                        ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
                                        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                                        ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                                        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
                                        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                                        ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                                        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                                        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                                        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                                        ((nb090AlphaDummy042 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)),
        ((nb090AlphaDummy676 A), (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A),
        (nb090AlphaDummy678 u)), ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
        ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A),
        (nb090AlphaDummy672 u)), ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
        ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A),
        (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
        ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A),
        (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A),
        (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
                                unfold nb090AlphaDummy673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
                                unfold nb090AlphaDummy674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                            ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                            ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                            ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
                            ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
                            ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                            ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                            ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
                            ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                            ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                            ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                            ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                            ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
                              unfold nb090AlphaDummy673;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                          (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
                              unfold nb090AlphaDummy674;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
                                unfold nb090AlphaDummy673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
                                unfold nb090AlphaDummy674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                            ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                            ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                            ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
                            ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
                            ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                            ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                            ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
                            ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                            ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                            ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                            ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                            ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy669 A) from (by
                        unfold nb090AlphaDummy669;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0694 A) 0))))
                    (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy671 u) from (by
                        unfold nb090AlphaDummy671;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0695 u) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy670 A) from (by
                          unfold nb090AlphaDummy670;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0694 A) 1))))
                      (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy672 u) from (by
                          unfold nb090AlphaDummy672;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0695 u) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy695 A) from (by
                            unfold nb090AlphaDummy695;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0724 A) 0))))
                        (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy696 u) from (by
                            unfold nb090AlphaDummy696;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0725 u) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy662 A) ≠ (nb090AlphaDummy693 A) from (by
                              unfold nb090AlphaDummy693;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0722 A) 0))))
                          (show (nb090AlphaDummy664 u) ≠ (nb090AlphaDummy694 u) from (by
                              unfold nb090AlphaDummy694;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0723 u) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy662 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy664 u))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy669 A) ≠
        (nb090AlphaDummy676 A) from (by
                                          unfold nb090AlphaDummy676;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0698 A) 1)))) (show
                                        (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy679 u)
                                        from (by
                                          unfold nb090AlphaDummy679;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0699 u) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy669 A) ≠
        (nb090AlphaDummy675 A) from (by
          unfold nb090AlphaDummy675;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0698 A) 0)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy678 u) from (by
          unfold nb090AlphaDummy678;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0699 u) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
          unfold nb090AlphaDummy673;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0696 A) 0)))) (show (nb090AlphaDummy671 u) ≠
        (nb090AlphaDummy674 u) from (by
          unfold nb090AlphaDummy674;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0697 u) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy677 A),
        (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A), (nb090AlphaDummy679 u)),
        ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)), ((nb090AlphaDummy673 A),
        (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
        ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)), ((nb090AlphaDummy695 A),
        (nb090AlphaDummy696 u)), ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
        ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)), ((nb090AlphaDummy661 A),
        (nb090AlphaDummy663 u)), ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
        ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)), ((nb090AlphaDummy653 A),
        (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)), ((nb090AlphaDummy657 A),
        (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0702
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0703
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0700
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0701
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy683 A) from (by
          unfold
            nb090AlphaDummy683;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0706
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy684 u) from (by
          unfold
            nb090AlphaDummy684;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0707
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy681 A) from (by
          unfold
            nb090AlphaDummy681;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0704
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy682 u) from (by
          unfold
            nb090AlphaDummy682;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0705
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy677 A), (nb090AlphaDummy680 u)), ((nb090AlphaDummy676 A),
        (nb090AlphaDummy679 u)), ((nb090AlphaDummy675 A), (nb090AlphaDummy678 u)),
        ((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)), ((nb090AlphaDummy669 A),
        (nb090AlphaDummy671 u)), ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
        ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)), ((nb090AlphaDummy693 A),
        (nb090AlphaDummy694 u)), ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
        ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)), ((nb090AlphaDummy691 A),
        (nb090AlphaDummy692 u)), ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
        ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)), ((nb090AlphaDummy655 A),
        (nb090AlphaDummy656 u)), ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠ (nb090AlphaDummy687 A) from (by
          unfold
            nb090AlphaDummy687;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0710
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy688 u) from (by
          unfold
            nb090AlphaDummy688;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0711
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy676 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0708
                    A)
                  0)))) (show (nb090AlphaDummy679 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0709
                    u)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy669
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy677 A) ≠ (nb090AlphaDummy689 A) from (by
          unfold
            nb090AlphaDummy689;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0714
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy690 u) from (by
          unfold
            nb090AlphaDummy690;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0715
                    u)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy677 A) ≠
        (nb090AlphaDummy685 A) from (by
          unfold
            nb090AlphaDummy685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0712
                    A)
                  0)))) (show (nb090AlphaDummy680 u) ≠ (nb090AlphaDummy686 u) from (by
          unfold
            nb090AlphaDummy686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0713
                    u)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                (by
                                  unfold nb090AlphaDummy673;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                              (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from
                                (by
                                  unfold nb090AlphaDummy674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                              ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                              ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                              ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
                              ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
                              ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                              ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                              ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
                              ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                              ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                              ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                              ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                              ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from (by
                                unfold nb090AlphaDummy673;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                            (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from (by
                                unfold nb090AlphaDummy674;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy669 A) ≠ (nb090AlphaDummy673 A) from
                                (by
                                  unfold nb090AlphaDummy673;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0696 A) 0))))
                              (show (nb090AlphaDummy671 u) ≠ (nb090AlphaDummy674 u) from
                                (by
                                  unfold nb090AlphaDummy674;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0697 u) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy673 A), (nb090AlphaDummy674 u)),
                              ((nb090AlphaDummy669 A), (nb090AlphaDummy671 u)),
                              ((nb090AlphaDummy670 A), (nb090AlphaDummy672 u)),
                              ((nb090AlphaDummy695 A), (nb090AlphaDummy696 u)),
                              ((nb090AlphaDummy693 A), (nb090AlphaDummy694 u)),
                              ((nb090AlphaDummy662 A), (nb090AlphaDummy664 u)),
                              ((nb090AlphaDummy661 A), (nb090AlphaDummy663 u)),
                              ((nb090AlphaDummy691 A), (nb090AlphaDummy692 u)),
                              ((nb090AlphaDummy665 A), (nb090AlphaDummy666 u)),
                              ((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
                              ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
                              ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
                              ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb090_wpp_notmem_1804 (A : Class) : (nb090AlphaDummy653 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy653, fv_syn_c1st] using (nb090_compact_fv_empty_0512 A)

theorem nb090_wpp_notmem_1805 (u : Var) : (nb090AlphaDummy654 u) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy654, fv_syn_c1st] using (nb090_compact_fv_empty_0513 u)

theorem nb090_wpp_notmem_1806 (A : Class) : (nb090AlphaDummy655 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy655, fv_syn_c1st] using (nb090_compact_fv_empty_0514 A)

theorem nb090_wpp_notmem_1807 (u : Var) : (nb090AlphaDummy656 u) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy656, fv_syn_c1st] using (nb090_compact_fv_empty_0515 u)

theorem nb090_wpp_notmem_1808 (A : Class) : (nb090AlphaDummy658 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy658, fv_syn_c1st] using (nb090_compact_fv_empty_0516 A)

theorem nb090_wpp_notmem_1809 (u : Var) : (nb090AlphaDummy660 u) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy660, fv_syn_c1st] using (nb090_compact_fv_empty_0517 u)

theorem nb090_wpp_notmem_1810 (A : Class) : (nb090AlphaDummy657 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy657, fv_syn_c1st] using (nb090_compact_fv_empty_0518 A)

theorem nb090_wpp_notmem_1811 (u : Var) : (nb090AlphaDummy659 u) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy659, fv_syn_c1st] using (nb090_compact_fv_empty_0519 u)

theorem nb090_wpp_notmem_1812 (A : Class) : (nb090AlphaDummy042 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy042, fv_syn_c1st] using (nb090_compact_fv_empty_0464 A)

theorem nb090_wpp_notmem_1813 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∉ ((synC1st)).fv := by
  simpa only [nb090AlphaDummy044, fv_syn_c1st] using
    (nb090_compact_fv_empty_0465 v u h)

theorem nb090_wpp_notmem_1814 (A : Class) : (nb090AlphaDummy041 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy041, fv_syn_c1st] using (nb090_compact_fv_empty_0462 A)

theorem nb090_wpp_notmem_1815 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∉ ((synC1st)).fv := by
  simpa only [nb090AlphaDummy043, fv_syn_c1st] using
    (nb090_compact_fv_empty_0463 v u h)

theorem nb090_wpp_notmem_1816 (A : Class) : (nb090AlphaDummy000 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy000, fv_syn_c1st] using (nb090_compact_fv_empty_0062 A)

theorem nb090_wpp_notmem_1817 (h : Var) : h ∉ ((synC1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0063 h)

theorem nb090_wpp_notmem_1818 (A : Class) : (nb090AlphaDummy002 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy002, fv_syn_c1st] using (nb090_compact_fv_empty_0020 A)

theorem nb090_wpp_notmem_1819 (v : Var) : v ∉ ((synC1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0021 v)

theorem nb090_wpp_notmem_1820 (A : Class) : (nb090AlphaDummy001 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy001, fv_syn_c1st] using (nb090_compact_fv_empty_0022 A)

theorem nb090_wpp_notmem_1821 (u : Var) : u ∉ ((synC1st)).fv := by
  simpa only [fv_syn_c1st] using (nb090_compact_fv_empty_0023 u)

theorem nb090_wpp_notmem_1822 (A : Class) : (nb090AlphaDummy003 A) ∉ ((synC1st)).fv :=
  by simpa only [nb090AlphaDummy003, fv_syn_c1st] using (nb090_compact_fv_empty_0024 A)

theorem nb090_wpp_notmem_1823 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉ ((synC1st)).fv := by
  simpa only [nb090AlphaDummy004, fv_syn_c1st] using
    (nb090_compact_fv_empty_0025 v u A h)

theorem nb090_compact_envfresh_0298 (v : Var) (u : Var) (A : Class) (h : Var) :
    TEnvFresh
      [((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC1st)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb090AlphaDummy653 A) (nb090AlphaDummy654 u)
      (nb090_wpp_notmem_1804 A) (nb090_wpp_notmem_1805 u)
      (TEnvFresh.consFresh (nb090AlphaDummy655 A) (nb090AlphaDummy656 u)
        (nb090_wpp_notmem_1806 A) (nb090_wpp_notmem_1807 u)
        (TEnvFresh.consFresh (nb090AlphaDummy658 A) (nb090AlphaDummy660 u)
          (nb090_wpp_notmem_1808 A) (nb090_wpp_notmem_1809 u)
          (TEnvFresh.consFresh (nb090AlphaDummy657 A) (nb090AlphaDummy659 u)
            (nb090_wpp_notmem_1810 A) (nb090_wpp_notmem_1811 u)
            (TEnvFresh.consFresh (nb090AlphaDummy042 A) (nb090AlphaDummy044 v u h)
              (nb090_wpp_notmem_1812 A) (nb090_wpp_notmem_1813 v u h)
              (TEnvFresh.consFresh (nb090AlphaDummy041 A) (nb090AlphaDummy043 v u h)
                (nb090_wpp_notmem_1814 A) (nb090_wpp_notmem_1815 v u h)
                (TEnvFresh.consFresh (nb090AlphaDummy000 A) h (nb090_wpp_notmem_1816 A)
                  (nb090_wpp_notmem_1817 h) (TEnvFresh.consFresh (nb090AlphaDummy002 A) v
                    (nb090_wpp_notmem_1818 A) (nb090_wpp_notmem_1819 v)
                    (TEnvFresh.consFresh (nb090AlphaDummy001 A) u
                      (nb090_wpp_notmem_1820 A) (nb090_wpp_notmem_1821 u)
                      (TEnvFresh.consFresh (nb090AlphaDummy003 A)
                        (nb090AlphaDummy004 v u A h) (nb090_wpp_notmem_1822 A)
                        (nb090_wpp_notmem_1823 v u A h)
                        (TEnvFresh.nil ((synC1st)).fv)))))))))))

/-- Checked nominal proof certificate identified upstream as `nb090_wpp_refl_0298`. -/
@[expose]
noncomputable def nb090WppRefl0298 (v : Var) (u : Var) (A : Class) (h : Var) :
    TReflOn
      [((nb090AlphaDummy653 A), (nb090AlphaDummy654 u)),
        ((nb090AlphaDummy655 A), (nb090AlphaDummy656 u)),
        ((nb090AlphaDummy658 A), (nb090AlphaDummy660 u)),
        ((nb090AlphaDummy657 A), (nb090AlphaDummy659 u)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      ((synC1st)).fv :=
  TEnvFresh.reflOn (nb090_compact_envfresh_0298 v u A h)


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
