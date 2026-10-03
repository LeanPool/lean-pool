/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block039

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part110`. -/


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
noncomputable def nb090_split_alpha_0088 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_721 A), (nb090_alpha_dummy_722 v u h)),
        ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
        ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
        ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
        ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
        ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
        ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
        ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
        ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
        ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_721 A))
          (Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_721 A))
            (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_722 v u h))
          (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_722 v u h))
            (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
                (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_716 A) from (by
                      unfold nb090_alpha_dummy_716;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
                  (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
                      unfold nb090_alpha_dummy_718;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_715 A) from (by
                        unfold nb090_alpha_dummy_715;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
                    (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_717 v u h) from (by
                        unfold nb090_alpha_dummy_717;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_721 A) from (by
                          unfold nb090_alpha_dummy_721;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0744 A) 0))))
                      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_722 v u h) from
                        (by
                          unfold nb090_alpha_dummy_722;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0745 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_719 A) from (by
                            unfold nb090_alpha_dummy_719;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0741 A) 0)))) (show
                          (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_720 v u h) from (by
                            unfold nb090_alpha_dummy_720;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0743 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_707 A) from (by
                              unfold nb090_alpha_dummy_707;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0734 A) 0)))) (show
                            (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_708 v u h) from
                            (by
                              unfold nb090_alpha_dummy_708;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0737 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_709 A) from (by
                                unfold nb090_alpha_dummy_709;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0735 A) 0)))) (show
                              (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_710 v u h) from
                              (by
                                unfold nb090_alpha_dummy_710;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0738 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_712 A) from
                                (by
                                  unfold nb090_alpha_dummy_712;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0736 A) 1)))) (show
                                (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_714 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_714;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                          1)))) (TAlphaVar.there (show
                                  (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_711 A) from (by
                                    unfold nb090_alpha_dummy_711;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0736 A)
                                            0)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                    (nb090_alpha_dummy_713 v u h) from (by
                                    unfold nb090_alpha_dummy_713;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_700 A) from
                                    (by
                                      unfold nb090_alpha_dummy_700;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0728 A)
                                              1)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                      (nb090_alpha_dummy_702 v u h) from (by
                                      unfold nb090_alpha_dummy_702;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0730 v u h) 1))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
                                        (nb090_alpha_dummy_699 A) from (by
                                        unfold nb090_alpha_dummy_699;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0728 A)
                                                0)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                        (nb090_alpha_dummy_701 v u h) from (by
                                        unfold nb090_alpha_dummy_701;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0730 v u h) 0))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
        (nb090_alpha_dummy_705 A) from (by
                                          unfold nb090_alpha_dummy_705;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0732 A) 0)))) (show
                                        (nb090_alpha_dummy_043 v u h) ≠
        (nb090_alpha_dummy_706 v u h) from (by
                                          unfold nb090_alpha_dummy_706;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0733 v u h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
        (nb090_alpha_dummy_703 A) from (by
          unfold nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0729 A) 0)))) (show (nb090_alpha_dummy_043 v u h) ≠
        (nb090_alpha_dummy_704 v u h) from (by
          unfold nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0731 v u h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv
        (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv
        (nb090_alpha_dummy_002 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv
        (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv
        (nb090_alpha_dummy_002 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv v))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_707 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_723 A) from (by
                              unfold nb090_alpha_dummy_723;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0746 A) 0)))) (show
                            (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_725 v u h) from
                            (by
                              unfold nb090_alpha_dummy_725;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_724 A) from (by
                                unfold nb090_alpha_dummy_724;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0746 A) 1)))) (show
                              (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_726 v u h) from
                              (by
                                unfold nb090_alpha_dummy_726;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_716 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_730 A) from (by
          unfold nb090_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 1)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_733 v u h) from (by
          unfold nb090_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_729 A) from (by
          unfold nb090_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 0)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_732 v u h) from (by
          unfold nb090_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_727 A) from (by
          unfold nb090_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A)
                  0)))) (show (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
        (by
          unfold nb090_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A),
        (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A),
        (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_730
        A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731
        A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731
        A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                      (by
                                        unfold nb090_alpha_dummy_727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090_alpha_dummy_725 v u h) ≠
                                        (nb090_alpha_dummy_728 v u h) from (by
                                        unfold nb090_alpha_dummy_728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                                    ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                                    ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                                    ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                                    ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                                    ((nb090_alpha_dummy_721 A), (nb090_alpha_dummy_722 v u h)),
                                    ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                                    ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                                    ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                                    ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                                    ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                                    ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                                    ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                                    ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                                    ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                                    ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                                    ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                    (by
                                      unfold nb090_alpha_dummy_727;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0748 A)
                                              0)))) (show (nb090_alpha_dummy_725 v u h) ≠
                                      (nb090_alpha_dummy_728 v u h) from (by
                                      unfold nb090_alpha_dummy_728;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0749 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                      (by
                                        unfold nb090_alpha_dummy_727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090_alpha_dummy_725 v u h) ≠
                                        (nb090_alpha_dummy_728 v u h) from (by
                                        unfold nb090_alpha_dummy_728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                                    ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                                    ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                                    ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                                    ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                                    ((nb090_alpha_dummy_721 A), (nb090_alpha_dummy_722 v u h)),
                                    ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                                    ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                                    ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                                    ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                                    ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                                    ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                                    ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                                    ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                                    ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
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
                    (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_716 A) from (by
                        unfold nb090_alpha_dummy_716;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
                    (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
                        unfold nb090_alpha_dummy_718;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_715 A) from (by
                          unfold nb090_alpha_dummy_715;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
                      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_717 v u h) from
                        (by
                          unfold nb090_alpha_dummy_717;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_721 A) from (by
                            unfold nb090_alpha_dummy_721;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0744 A) 0)))) (show
                          (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_722 v u h) from (by
                            unfold nb090_alpha_dummy_722;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0745 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_719 A) from (by
                              unfold nb090_alpha_dummy_719;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0741 A) 0)))) (show
                            (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_720 v u h) from
                            (by
                              unfold nb090_alpha_dummy_720;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0743 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_707 A) from (by
                                unfold nb090_alpha_dummy_707;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0734 A) 0)))) (show
                              (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_708 v u h) from
                              (by
                                unfold nb090_alpha_dummy_708;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0737 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_709 A) from
                                (by
                                  unfold nb090_alpha_dummy_709;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0735 A) 0)))) (show
                                (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_710 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_710;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0738 v u h)
                                          0)))) (TAlphaVar.there (show
                                  (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_712 A) from (by
                                    unfold nb090_alpha_dummy_712;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0736 A)
                                            1)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                    (nb090_alpha_dummy_714 v u h) from (by
                                    unfold nb090_alpha_dummy_714;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_711 A) from
                                    (by
                                      unfold nb090_alpha_dummy_711;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0736 A)
                                              0)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                      (nb090_alpha_dummy_713 v u h) from (by
                                      unfold nb090_alpha_dummy_713;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0739 v u h) 0))))
                                  (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
                                        (nb090_alpha_dummy_700 A) from (by
                                        unfold nb090_alpha_dummy_700;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0728 A)
                                                1)))) (show (nb090_alpha_dummy_043 v u h) ≠
                                        (nb090_alpha_dummy_702 v u h) from (by
                                        unfold nb090_alpha_dummy_702;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0730 v u h) 1))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
        (nb090_alpha_dummy_699 A) from (by
                                          unfold nb090_alpha_dummy_699;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0728 A) 0)))) (show
                                        (nb090_alpha_dummy_043 v u h) ≠
        (nb090_alpha_dummy_701 v u h) from (by
                                          unfold nb090_alpha_dummy_701;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0730 v u h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_041 A) ≠
        (nb090_alpha_dummy_705 A) from (by
          unfold nb090_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0732 A) 0)))) (show (nb090_alpha_dummy_043 v u h) ≠
        (nb090_alpha_dummy_706 v u h) from (by
          unfold nb090_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0733 v u h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_703 A) from (by
          unfold nb090_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0729 A) 0)))) (show (nb090_alpha_dummy_043 v u h) ≠
        (nb090_alpha_dummy_704 v u h) from (by
          unfold nb090_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0731 v u h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv
        (nb090_alpha_dummy_001 A)))).fv ∪ ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002
        A)))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_707 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_723 A) from (by
                                unfold nb090_alpha_dummy_723;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0746 A) 0)))) (show
                              (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_725 v u h) from
                              (by
                                unfold nb090_alpha_dummy_725;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_724 A) from
                                (by
                                  unfold nb090_alpha_dummy_724;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0746 A) 1)))) (show
                                (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_726 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_726;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_716 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_730 A) from (by
          unfold nb090_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 1)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_733 v u h) from (by
          unfold nb090_alpha_dummy_733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  1)))) (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_729 A) from (by
          unfold nb090_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A)
                  0)))) (show (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_732 v u h) from
        (by
          unfold nb090_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_727 A) from (by
          unfold nb090_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A)
                  0)))) (show (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
        (by
          unfold nb090_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A),
        (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_721 A),
        (nb090_alpha_dummy_722 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_730
        A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731
        A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731
        A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A)
                                        from (by
                                          unfold nb090_alpha_dummy_727;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0748 A) 0)))) (show
                                        (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_728 v u h) from (by
                                          unfold nb090_alpha_dummy_728;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0749 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                                      ((nb090_alpha_dummy_723 A),
                                        (nb090_alpha_dummy_725 v u h)),
                                      ((nb090_alpha_dummy_724 A),
                                        (nb090_alpha_dummy_726 v u h)),
                                      ((nb090_alpha_dummy_716 A),
                                        (nb090_alpha_dummy_718 v u h)),
                                      ((nb090_alpha_dummy_715 A),
                                        (nb090_alpha_dummy_717 v u h)),
                                      ((nb090_alpha_dummy_721 A),
                                        (nb090_alpha_dummy_722 v u h)),
                                      ((nb090_alpha_dummy_719 A),
                                        (nb090_alpha_dummy_720 v u h)),
                                      ((nb090_alpha_dummy_707 A),
                                        (nb090_alpha_dummy_708 v u h)),
                                      ((nb090_alpha_dummy_709 A),
                                        (nb090_alpha_dummy_710 v u h)),
                                      ((nb090_alpha_dummy_712 A),
                                        (nb090_alpha_dummy_714 v u h)),
                                      ((nb090_alpha_dummy_711 A),
                                        (nb090_alpha_dummy_713 v u h)),
                                      ((nb090_alpha_dummy_700 A),
                                        (nb090_alpha_dummy_702 v u h)),
                                      ((nb090_alpha_dummy_699 A),
                                        (nb090_alpha_dummy_701 v u h)),
                                      ((nb090_alpha_dummy_705 A),
                                        (nb090_alpha_dummy_706 v u h)),
                                      ((nb090_alpha_dummy_703 A),
                                        (nb090_alpha_dummy_704 v u h)),
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
                                      (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                      (by
                                        unfold nb090_alpha_dummy_727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090_alpha_dummy_725 v u h) ≠
                                        (nb090_alpha_dummy_728 v u h) from (by
                                        unfold nb090_alpha_dummy_728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A)
                                        from (by
                                          unfold nb090_alpha_dummy_727;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0748 A) 0)))) (show
                                        (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_728 v u h) from (by
                                          unfold nb090_alpha_dummy_728;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0749 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                                      ((nb090_alpha_dummy_723 A),
                                        (nb090_alpha_dummy_725 v u h)),
                                      ((nb090_alpha_dummy_724 A),
                                        (nb090_alpha_dummy_726 v u h)),
                                      ((nb090_alpha_dummy_716 A),
                                        (nb090_alpha_dummy_718 v u h)),
                                      ((nb090_alpha_dummy_715 A),
                                        (nb090_alpha_dummy_717 v u h)),
                                      ((nb090_alpha_dummy_721 A),
                                        (nb090_alpha_dummy_722 v u h)),
                                      ((nb090_alpha_dummy_719 A),
                                        (nb090_alpha_dummy_720 v u h)),
                                      ((nb090_alpha_dummy_707 A),
                                        (nb090_alpha_dummy_708 v u h)),
                                      ((nb090_alpha_dummy_709 A),
                                        (nb090_alpha_dummy_710 v u h)),
                                      ((nb090_alpha_dummy_712 A),
                                        (nb090_alpha_dummy_714 v u h)),
                                      ((nb090_alpha_dummy_711 A),
                                        (nb090_alpha_dummy_713 v u h)),
                                      ((nb090_alpha_dummy_700 A),
                                        (nb090_alpha_dummy_702 v u h)),
                                      ((nb090_alpha_dummy_699 A),
                                        (nb090_alpha_dummy_701 v u h)),
                                      ((nb090_alpha_dummy_705 A),
                                        (nb090_alpha_dummy_706 v u h)),
                                      ((nb090_alpha_dummy_703 A),
                                        (nb090_alpha_dummy_704 v u h)),
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

/-! Certificates from `NAR4C090C001Part111`. -/


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
noncomputable def nb090_split_alpha_0089 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_749 A), (nb090_alpha_dummy_750 v u h)),
        ((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)),
        ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
        ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
        ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)),
        ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
        ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
        ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
        ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
        ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
        ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
        ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
        ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
        ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
        ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
        ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_749 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_749 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_750 v u h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_750 v u h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_723 A) from (by
                      unfold nb090_alpha_dummy_723;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0746 A) 0))))
                  (show (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_725 v u h) from (by
                      unfold nb090_alpha_dummy_725;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_724 A) from (by
                        unfold nb090_alpha_dummy_724;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0746 A) 1))))
                    (show (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_726 v u h) from (by
                        unfold nb090_alpha_dummy_726;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0747 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_749 A) from (by
                          unfold nb090_alpha_dummy_749;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0776 A) 0))))
                      (show (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_750 v u h) from
                        (by
                          unfold nb090_alpha_dummy_750;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0777 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_747 A) from (by
                            unfold nb090_alpha_dummy_747;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0774 A) 0)))) (show
                          (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_748 v u h) from (by
                            unfold nb090_alpha_dummy_748;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0775 v u h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_716 A))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_718 v u h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_730 A) from
                                      (by
                                        unfold nb090_alpha_dummy_730;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0750 A)
                                                1)))) (show (nb090_alpha_dummy_725 v u h) ≠
                                        (nb090_alpha_dummy_733 v u h) from (by
                                        unfold nb090_alpha_dummy_733;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0751 v u h) 1))))
                                    (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_729 A) from (by
                                          unfold nb090_alpha_dummy_729;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0750 A) 0)))) (show
                                        (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_732 v u h) from (by
                                          unfold nb090_alpha_dummy_732;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0751 v u h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_727 A) from (by
          unfold nb090_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A) 0)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_728 v u h) from (by
          unfold nb090_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_731 A),
        (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_749 A),
        (nb090_alpha_dummy_750 v u h)), ((nb090_alpha_dummy_747 A),
        (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A),
        (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_731 A),
        (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_749 A),
        (nb090_alpha_dummy_750 v u h)), ((nb090_alpha_dummy_747 A),
        (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A),
        (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from (by
                                unfold nb090_alpha_dummy_727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
                              (by
                                unfold nb090_alpha_dummy_728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                            ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                            ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                            ((nb090_alpha_dummy_749 A), (nb090_alpha_dummy_750 v u h)),
                            ((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)),
                            ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                            ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                            ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)),
                            ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                            ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                            ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                            ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                            ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                            ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                            ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                            ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                            ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from (by
                              unfold nb090_alpha_dummy_727;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                            (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
                            (by
                              unfold nb090_alpha_dummy_728;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0749 v u h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from (by
                                unfold nb090_alpha_dummy_727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
                              (by
                                unfold nb090_alpha_dummy_728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                            ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                            ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                            ((nb090_alpha_dummy_749 A), (nb090_alpha_dummy_750 v u h)),
                            ((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)),
                            ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                            ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                            ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)),
                            ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                            ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                            ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                            ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                            ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                            ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                            ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                            ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                            ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                            ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                            ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_723 A) from (by
                        unfold nb090_alpha_dummy_723;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0746 A) 0))))
                    (show (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_725 v u h) from (by
                        unfold nb090_alpha_dummy_725;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_724 A) from (by
                          unfold nb090_alpha_dummy_724;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0746 A) 1))))
                      (show (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_726 v u h) from
                        (by
                          unfold nb090_alpha_dummy_726;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0747 v u h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_749 A) from (by
                            unfold nb090_alpha_dummy_749;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0776 A) 0)))) (show
                          (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_750 v u h) from (by
                            unfold nb090_alpha_dummy_750;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0777 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_716 A) ≠ (nb090_alpha_dummy_747 A) from (by
                              unfold nb090_alpha_dummy_747;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0774 A) 0)))) (show
                            (nb090_alpha_dummy_718 v u h) ≠ (nb090_alpha_dummy_748 v u h) from
                            (by
                              unfold nb090_alpha_dummy_748;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0775 v u h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_716 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_718 v u h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_730 A) from (by
                                          unfold nb090_alpha_dummy_730;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0750 A) 1)))) (show
                                        (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_733 v u h) from (by
                                          unfold nb090_alpha_dummy_733;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0751 v u h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_723 A) ≠
        (nb090_alpha_dummy_729 A) from (by
          unfold nb090_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 0)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_732 v u h) from (by
          unfold nb090_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from (by
          unfold nb090_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A) 0)))) (show (nb090_alpha_dummy_725 v u h) ≠
        (nb090_alpha_dummy_728 v u h) from (by
          unfold nb090_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_731 A),
        (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_749 A),
        (nb090_alpha_dummy_750 v u h)), ((nb090_alpha_dummy_747 A),
        (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A),
        (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_737 A) from (by
          unfold
            nb090_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_738 v u h) from
        (by
          unfold
            nb090_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_735 A) from (by
          unfold
            nb090_alpha_dummy_735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_736 v u h) from
        (by
          unfold
            nb090_alpha_dummy_736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_731 A), (nb090_alpha_dummy_734 v u h)), ((nb090_alpha_dummy_730 A),
        (nb090_alpha_dummy_733 v u h)), ((nb090_alpha_dummy_729 A),
        (nb090_alpha_dummy_732 v u h)), ((nb090_alpha_dummy_727 A),
        (nb090_alpha_dummy_728 v u h)), ((nb090_alpha_dummy_723 A),
        (nb090_alpha_dummy_725 v u h)), ((nb090_alpha_dummy_724 A),
        (nb090_alpha_dummy_726 v u h)), ((nb090_alpha_dummy_749 A),
        (nb090_alpha_dummy_750 v u h)), ((nb090_alpha_dummy_747 A),
        (nb090_alpha_dummy_748 v u h)), ((nb090_alpha_dummy_716 A),
        (nb090_alpha_dummy_718 v u h)), ((nb090_alpha_dummy_715 A),
        (nb090_alpha_dummy_717 v u h)), ((nb090_alpha_dummy_745 A),
        (nb090_alpha_dummy_746 v u h)), ((nb090_alpha_dummy_719 A),
        (nb090_alpha_dummy_720 v u h)), ((nb090_alpha_dummy_707 A),
        (nb090_alpha_dummy_708 v u h)), ((nb090_alpha_dummy_709 A),
        (nb090_alpha_dummy_710 v u h)), ((nb090_alpha_dummy_712 A),
        (nb090_alpha_dummy_714 v u h)), ((nb090_alpha_dummy_711 A),
        (nb090_alpha_dummy_713 v u h)), ((nb090_alpha_dummy_700 A),
        (nb090_alpha_dummy_702 v u h)), ((nb090_alpha_dummy_699 A),
        (nb090_alpha_dummy_701 v u h)), ((nb090_alpha_dummy_705 A),
        (nb090_alpha_dummy_706 v u h)), ((nb090_alpha_dummy_703 A),
        (nb090_alpha_dummy_704 v u h)), ((nb090_alpha_dummy_042 A),
        (nb090_alpha_dummy_044 v u h)), ((nb090_alpha_dummy_041 A),
        (nb090_alpha_dummy_043 v u h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠ (nb090_alpha_dummy_741 A) from (by
          unfold
            nb090_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_742 v u h) from
        (by
          unfold
            nb090_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_730 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090_alpha_dummy_733 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_723
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_731 A) ≠ (nb090_alpha_dummy_743 A) from (by
          unfold
            nb090_alpha_dummy_743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_744 v u h) from
        (by
          unfold
            nb090_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_731 A) ≠
        (nb090_alpha_dummy_739 A) from (by
          unfold
            nb090_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090_alpha_dummy_734 v u h) ≠ (nb090_alpha_dummy_740 v u h) from
        (by
          unfold
            nb090_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                (by
                                  unfold nb090_alpha_dummy_727;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                                (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_728;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                              ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                              ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                              ((nb090_alpha_dummy_749 A), (nb090_alpha_dummy_750 v u h)),
                              ((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)),
                              ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                              ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                              ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)),
                              ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                              ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                              ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                              ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                              ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                              ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                              ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                              ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                              ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from (by
                                unfold nb090_alpha_dummy_727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h) from
                              (by
                                unfold nb090_alpha_dummy_728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_723 A) ≠ (nb090_alpha_dummy_727 A) from
                                (by
                                  unfold nb090_alpha_dummy_727;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                                (nb090_alpha_dummy_725 v u h) ≠ (nb090_alpha_dummy_728 v u h)
                                from (by
                                  unfold nb090_alpha_dummy_728;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_727 A), (nb090_alpha_dummy_728 v u h)),
                              ((nb090_alpha_dummy_723 A), (nb090_alpha_dummy_725 v u h)),
                              ((nb090_alpha_dummy_724 A), (nb090_alpha_dummy_726 v u h)),
                              ((nb090_alpha_dummy_749 A), (nb090_alpha_dummy_750 v u h)),
                              ((nb090_alpha_dummy_747 A), (nb090_alpha_dummy_748 v u h)),
                              ((nb090_alpha_dummy_716 A), (nb090_alpha_dummy_718 v u h)),
                              ((nb090_alpha_dummy_715 A), (nb090_alpha_dummy_717 v u h)),
                              ((nb090_alpha_dummy_745 A), (nb090_alpha_dummy_746 v u h)),
                              ((nb090_alpha_dummy_719 A), (nb090_alpha_dummy_720 v u h)),
                              ((nb090_alpha_dummy_707 A), (nb090_alpha_dummy_708 v u h)),
                              ((nb090_alpha_dummy_709 A), (nb090_alpha_dummy_710 v u h)),
                              ((nb090_alpha_dummy_712 A), (nb090_alpha_dummy_714 v u h)),
                              ((nb090_alpha_dummy_711 A), (nb090_alpha_dummy_713 v u h)),
                              ((nb090_alpha_dummy_700 A), (nb090_alpha_dummy_702 v u h)),
                              ((nb090_alpha_dummy_699 A), (nb090_alpha_dummy_701 v u h)),
                              ((nb090_alpha_dummy_705 A), (nb090_alpha_dummy_706 v u h)),
                              ((nb090_alpha_dummy_703 A), (nb090_alpha_dummy_704 v u h)),
                              ((nb090_alpha_dummy_042 A), (nb090_alpha_dummy_044 v u h)),
                              ((nb090_alpha_dummy_041 A), (nb090_alpha_dummy_043 v u h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
