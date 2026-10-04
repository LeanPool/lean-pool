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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0088`. -/
@[expose]
noncomputable def nb090SplitAlpha0088 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy721 A), (nb090AlphaDummy722 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
        ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
        ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
        ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
        ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
        ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
        ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy721 A))
          (Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy721 A))
            (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCphi (Class.cv (nb090AlphaDummy716 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy722 v u h))
          (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy722 v u h))
            (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
                (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy716 A) from (by
                      unfold nb090AlphaDummy716;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
                  (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
                      unfold nb090AlphaDummy718;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy715 A) from (by
                        unfold nb090AlphaDummy715;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
                    (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy717 v u h) from (by
                        unfold nb090AlphaDummy717;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy721 A) from (by
                          unfold nb090AlphaDummy721;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0744 A) 0))))
                      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy722 v u h) from
                        (by
                          unfold nb090AlphaDummy722;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0745 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy719 A) from (by
                            unfold nb090AlphaDummy719;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0741 A) 0)))) (show
                          (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy720 v u h) from (by
                            unfold nb090AlphaDummy720;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0743 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy707 A) from (by
                              unfold nb090AlphaDummy707;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0734 A) 0)))) (show
                            (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy708 v u h) from
                            (by
                              unfold nb090AlphaDummy708;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0737 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy709 A) from (by
                                unfold nb090AlphaDummy709;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0735 A) 0)))) (show
                              (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy710 v u h) from
                              (by
                                unfold nb090AlphaDummy710;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0738 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy712 A) from
                                (by
                                  unfold nb090AlphaDummy712;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0736 A) 1)))) (show
                                (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy714 v u h)
                                from (by
                                  unfold nb090AlphaDummy714;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                          1)))) (TAlphaVar.there (show
                                  (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy711 A) from (by
                                    unfold nb090AlphaDummy711;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0736 A)
                                            0)))) (show (nb090AlphaDummy043 v u h) ≠
                                    (nb090AlphaDummy713 v u h) from (by
                                    unfold nb090AlphaDummy713;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy700 A) from
                                    (by
                                      unfold nb090AlphaDummy700;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0728 A)
                                              1)))) (show (nb090AlphaDummy043 v u h) ≠
                                      (nb090AlphaDummy702 v u h) from (by
                                      unfold nb090AlphaDummy702;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0730 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
                                        (nb090AlphaDummy699 A) from (by
                                        unfold nb090AlphaDummy699;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0728 A)
                                                0)))) (show (nb090AlphaDummy043 v u h) ≠
                                        (nb090AlphaDummy701 v u h) from (by
                                        unfold nb090AlphaDummy701;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0730 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
        (nb090AlphaDummy705 A) from (by
                                          unfold nb090AlphaDummy705;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0732 A) 0)))) (show
                                        (nb090AlphaDummy043 v u h) ≠
        (nb090AlphaDummy706 v u h) from (by
                                          unfold nb090AlphaDummy706;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0733 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0729 A) 0)))) (show (nb090AlphaDummy043 v u h) ≠
        (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0731 v u h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCfv (synC1st) (Class.cv
        (nb090AlphaDummy001 A)))).fv ∪ ((synCfv (synC1st) (Class.cv
        (nb090AlphaDummy002 A)))).fv ∪ ((synCfv (synC2nd) (Class.cv
        (nb090AlphaDummy001 A)))).fv ∪ ((synCfv (synC2nd) (Class.cv
        (nb090AlphaDummy002 A)))).fv) (by decide)) (freshVar_injective (((Class.cv h)).fv ∪
        ((synCfv (synC1st) (Class.cv u))).fv ∪ ((synCfv (synC1st) (Class.cv v))).fv ∪
        ((synCfv (synC2nd) (Class.cv u))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy041 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
                      ((Class.cv (nb090AlphaDummy708 v u h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy723 A) from (by
                              unfold nb090AlphaDummy723;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0746 A) 0)))) (show
                            (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy725 v u h) from
                            (by
                              unfold nb090AlphaDummy725;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy724 A) from (by
                                unfold nb090AlphaDummy724;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0746 A) 1)))) (show
                              (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy726 v u h) from
                              (by
                                unfold nb090AlphaDummy726;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy716 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090AlphaDummy718 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy730 A) from (by
          unfold nb090AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 1)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy733 v u h) from (by
          unfold nb090AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy729 A) from (by
          unfold nb090AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 0)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy732 v u h) from (by
          unfold nb090AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy727 A) from (by
          unfold nb090AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A)
                  0)))) (show (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
        (by
          unfold nb090AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy731 A), (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy721 A),
        (nb090AlphaDummy722 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy731 A), (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy721 A),
        (nb090AlphaDummy722 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy730
        A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731
        A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731
        A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                      (by
                                        unfold nb090AlphaDummy727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090AlphaDummy725 v u h) ≠
                                        (nb090AlphaDummy728 v u h) from (by
                                        unfold nb090AlphaDummy728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                                    ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                                    ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                                    ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                                    ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                                    ((nb090AlphaDummy721 A), (nb090AlphaDummy722 v u h)),
                                    ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                                    ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                                    ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                                    ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                                    ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                                    ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                                    ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                                    ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                                    ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                                    ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                                    ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                    (by
                                      unfold nb090AlphaDummy727;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0748 A)
                                              0)))) (show (nb090AlphaDummy725 v u h) ≠
                                      (nb090AlphaDummy728 v u h) from (by
                                      unfold nb090AlphaDummy728;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0749 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                      (by
                                        unfold nb090AlphaDummy727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090AlphaDummy725 v u h) ≠
                                        (nb090AlphaDummy728 v u h) from (by
                                        unfold nb090AlphaDummy728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                                    ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                                    ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                                    ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                                    ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                                    ((nb090AlphaDummy721 A), (nb090AlphaDummy722 v u h)),
                                    ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                                    ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                                    ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                                    ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                                    ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                                    ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                                    ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                                    ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                                    ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
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
                    (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy716 A) from (by
                        unfold nb090AlphaDummy716;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
                    (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
                        unfold nb090AlphaDummy718;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy715 A) from (by
                          unfold nb090AlphaDummy715;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
                      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy717 v u h) from
                        (by
                          unfold nb090AlphaDummy717;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy721 A) from (by
                            unfold nb090AlphaDummy721;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0744 A) 0)))) (show
                          (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy722 v u h) from (by
                            unfold nb090AlphaDummy722;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0745 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy719 A) from (by
                              unfold nb090AlphaDummy719;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0741 A) 0)))) (show
                            (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy720 v u h) from
                            (by
                              unfold nb090AlphaDummy720;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0743 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy707 A) from (by
                                unfold nb090AlphaDummy707;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0734 A) 0)))) (show
                              (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy708 v u h) from
                              (by
                                unfold nb090AlphaDummy708;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0737 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy709 A) from
                                (by
                                  unfold nb090AlphaDummy709;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0735 A) 0)))) (show
                                (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy710 v u h)
                                from (by
                                  unfold nb090AlphaDummy710;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0738 v u h)
                                          0)))) (TAlphaVar.there (show
                                  (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy712 A) from (by
                                    unfold nb090AlphaDummy712;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0736 A)
                                            1)))) (show (nb090AlphaDummy043 v u h) ≠
                                    (nb090AlphaDummy714 v u h) from (by
                                    unfold nb090AlphaDummy714;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0739 v u h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy711 A) from
                                    (by
                                      unfold nb090AlphaDummy711;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0736 A)
                                              0)))) (show (nb090AlphaDummy043 v u h) ≠
                                      (nb090AlphaDummy713 v u h) from (by
                                      unfold nb090AlphaDummy713;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0739 v u h) 0))))
                                  (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
                                        (nb090AlphaDummy700 A) from (by
                                        unfold nb090AlphaDummy700;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0728 A)
                                                1)))) (show (nb090AlphaDummy043 v u h) ≠
                                        (nb090AlphaDummy702 v u h) from (by
                                        unfold nb090AlphaDummy702;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0730 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
        (nb090AlphaDummy699 A) from (by
                                          unfold nb090AlphaDummy699;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0728 A) 0)))) (show
                                        (nb090AlphaDummy043 v u h) ≠
        (nb090AlphaDummy701 v u h) from (by
                                          unfold nb090AlphaDummy701;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0730 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy041 A) ≠
        (nb090AlphaDummy705 A) from (by
          unfold nb090AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0732 A) 0)))) (show (nb090AlphaDummy043 v u h) ≠
        (nb090AlphaDummy706 v u h) from (by
          unfold nb090AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0733 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0729 A) 0)))) (show (nb090AlphaDummy043 v u h) ≠
        (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0731 v u h) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCfv (synC1st) (Class.cv
        (nb090AlphaDummy001 A)))).fv ∪ ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002
        A)))).fv ∪ ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) (by decide))
        (freshVar_injective (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
        ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy041 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
                        ((Class.cv (nb090AlphaDummy708 v u h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy723 A) from (by
                                unfold nb090AlphaDummy723;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0746 A) 0)))) (show
                              (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy725 v u h) from
                              (by
                                unfold nb090AlphaDummy725;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy724 A) from
                                (by
                                  unfold nb090AlphaDummy724;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0746 A) 1)))) (show
                                (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy726 v u h)
                                from (by
                                  unfold nb090AlphaDummy726;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0747 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy716 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy718 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy730 A) from (by
          unfold nb090AlphaDummy730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 1)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy733 v u h) from (by
          unfold nb090AlphaDummy733;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy729 A) from (by
          unfold nb090AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A)
                  0)))) (show (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy732 v u h) from
        (by
          unfold nb090AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy727 A) from (by
          unfold nb090AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A)
                  0)))) (show (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
        (by
          unfold nb090AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy731 A), (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy721 A),
        (nb090AlphaDummy722 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy731 A), (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy721 A),
        (nb090AlphaDummy722 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy730
        A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731
        A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731
        A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A)
                                        from (by
                                          unfold nb090AlphaDummy727;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0748 A) 0)))) (show
                                        (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy728 v u h) from (by
                                          unfold nb090AlphaDummy728;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0749 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                                      ((nb090AlphaDummy723 A),
                                        (nb090AlphaDummy725 v u h)),
                                      ((nb090AlphaDummy724 A),
                                        (nb090AlphaDummy726 v u h)),
                                      ((nb090AlphaDummy716 A),
                                        (nb090AlphaDummy718 v u h)),
                                      ((nb090AlphaDummy715 A),
                                        (nb090AlphaDummy717 v u h)),
                                      ((nb090AlphaDummy721 A),
                                        (nb090AlphaDummy722 v u h)),
                                      ((nb090AlphaDummy719 A),
                                        (nb090AlphaDummy720 v u h)),
                                      ((nb090AlphaDummy707 A),
                                        (nb090AlphaDummy708 v u h)),
                                      ((nb090AlphaDummy709 A),
                                        (nb090AlphaDummy710 v u h)),
                                      ((nb090AlphaDummy712 A),
                                        (nb090AlphaDummy714 v u h)),
                                      ((nb090AlphaDummy711 A),
                                        (nb090AlphaDummy713 v u h)),
                                      ((nb090AlphaDummy700 A),
                                        (nb090AlphaDummy702 v u h)),
                                      ((nb090AlphaDummy699 A),
                                        (nb090AlphaDummy701 v u h)),
                                      ((nb090AlphaDummy705 A),
                                        (nb090AlphaDummy706 v u h)),
                                      ((nb090AlphaDummy703 A),
                                        (nb090AlphaDummy704 v u h)),
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
                                      (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                      (by
                                        unfold nb090AlphaDummy727;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0748 A)
                                                0)))) (show (nb090AlphaDummy725 v u h) ≠
                                        (nb090AlphaDummy728 v u h) from (by
                                        unfold nb090AlphaDummy728;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0749 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A)
                                        from (by
                                          unfold nb090AlphaDummy727;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0748 A) 0)))) (show
                                        (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy728 v u h) from (by
                                          unfold nb090AlphaDummy728;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0749 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                                      ((nb090AlphaDummy723 A),
                                        (nb090AlphaDummy725 v u h)),
                                      ((nb090AlphaDummy724 A),
                                        (nb090AlphaDummy726 v u h)),
                                      ((nb090AlphaDummy716 A),
                                        (nb090AlphaDummy718 v u h)),
                                      ((nb090AlphaDummy715 A),
                                        (nb090AlphaDummy717 v u h)),
                                      ((nb090AlphaDummy721 A),
                                        (nb090AlphaDummy722 v u h)),
                                      ((nb090AlphaDummy719 A),
                                        (nb090AlphaDummy720 v u h)),
                                      ((nb090AlphaDummy707 A),
                                        (nb090AlphaDummy708 v u h)),
                                      ((nb090AlphaDummy709 A),
                                        (nb090AlphaDummy710 v u h)),
                                      ((nb090AlphaDummy712 A),
                                        (nb090AlphaDummy714 v u h)),
                                      ((nb090AlphaDummy711 A),
                                        (nb090AlphaDummy713 v u h)),
                                      ((nb090AlphaDummy700 A),
                                        (nb090AlphaDummy702 v u h)),
                                      ((nb090AlphaDummy699 A),
                                        (nb090AlphaDummy701 v u h)),
                                      ((nb090AlphaDummy705 A),
                                        (nb090AlphaDummy706 v u h)),
                                      ((nb090AlphaDummy703 A),
                                        (nb090AlphaDummy704 v u h)),
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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0089`. -/
@[expose]
noncomputable def nb090SplitAlpha0089 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy749 A), (nb090AlphaDummy750 v u h)),
        ((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)),
        ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
        ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
        ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
        ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
        ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
        ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
        ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
        ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
        ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy749 A))
          (synCphi (Class.cv (nb090AlphaDummy716 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy749 A))
            (synCphi (Class.cv (nb090AlphaDummy716 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy750 v u h))
          (synCphi (Class.cv (nb090AlphaDummy718 v u h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy750 v u h))
            (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy723 A) from (by
                      unfold nb090AlphaDummy723;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0746 A) 0))))
                  (show (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy725 v u h) from (by
                      unfold nb090AlphaDummy725;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy724 A) from (by
                        unfold nb090AlphaDummy724;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0746 A) 1))))
                    (show (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy726 v u h) from (by
                        unfold nb090AlphaDummy726;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0747 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy749 A) from (by
                          unfold nb090AlphaDummy749;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0776 A) 0))))
                      (show (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy750 v u h) from
                        (by
                          unfold nb090AlphaDummy750;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0777 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy747 A) from (by
                            unfold nb090AlphaDummy747;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0774 A) 0)))) (show
                          (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy748 v u h) from (by
                            unfold nb090AlphaDummy748;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0775 v u h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy716 A))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy718 v u h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy730 A) from
                                      (by
                                        unfold nb090AlphaDummy730;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0750 A)
                                                1)))) (show (nb090AlphaDummy725 v u h) ≠
                                        (nb090AlphaDummy733 v u h) from (by
                                        unfold nb090AlphaDummy733;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0751 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy729 A) from (by
                                          unfold nb090AlphaDummy729;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0750 A) 0)))) (show
                                        (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy732 v u h) from (by
                                          unfold nb090AlphaDummy732;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0751 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy727 A) from (by
          unfold nb090AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A) 0)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy728 v u h) from (by
          unfold nb090AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy731 A),
        (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy749 A),
        (nb090AlphaDummy750 v u h)), ((nb090AlphaDummy747 A),
        (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy745 A),
        (nb090AlphaDummy746 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy731 A),
        (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy749 A),
        (nb090AlphaDummy750 v u h)), ((nb090AlphaDummy747 A),
        (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy745 A),
        (nb090AlphaDummy746 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from (by
                                unfold nb090AlphaDummy727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
                              (by
                                unfold nb090AlphaDummy728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                            ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                            ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                            ((nb090AlphaDummy749 A), (nb090AlphaDummy750 v u h)),
                            ((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)),
                            ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                            ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                            ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
                            ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                            ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                            ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                            ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                            ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                            ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                            ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                            ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                            ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from (by
                              unfold nb090AlphaDummy727;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                            (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
                            (by
                              unfold nb090AlphaDummy728;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0749 v u h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from (by
                                unfold nb090AlphaDummy727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
                              (by
                                unfold nb090AlphaDummy728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                            ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                            ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                            ((nb090AlphaDummy749 A), (nb090AlphaDummy750 v u h)),
                            ((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)),
                            ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                            ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                            ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
                            ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                            ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                            ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                            ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                            ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                            ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                            ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                            ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                            ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                            ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                            ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy723 A) from (by
                        unfold nb090AlphaDummy723;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0746 A) 0))))
                    (show (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy725 v u h) from (by
                        unfold nb090AlphaDummy725;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0747 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy724 A) from (by
                          unfold nb090AlphaDummy724;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0746 A) 1))))
                      (show (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy726 v u h) from
                        (by
                          unfold nb090AlphaDummy726;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0747 v u h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy749 A) from (by
                            unfold nb090AlphaDummy749;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0776 A) 0)))) (show
                          (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy750 v u h) from (by
                            unfold nb090AlphaDummy750;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0777 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy716 A) ≠ (nb090AlphaDummy747 A) from (by
                              unfold nb090AlphaDummy747;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0774 A) 0)))) (show
                            (nb090AlphaDummy718 v u h) ≠ (nb090AlphaDummy748 v u h) from
                            (by
                              unfold nb090AlphaDummy748;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0775 v u h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy716 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy718 v u h))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy730 A) from (by
                                          unfold nb090AlphaDummy730;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0750 A) 1)))) (show
                                        (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy733 v u h) from (by
                                          unfold nb090AlphaDummy733;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0751 v u h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy723 A) ≠
        (nb090AlphaDummy729 A) from (by
          unfold nb090AlphaDummy729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0750 A) 0)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy732 v u h) from (by
          unfold nb090AlphaDummy732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0751 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from (by
          unfold nb090AlphaDummy727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0748 A) 0)))) (show (nb090AlphaDummy725 v u h) ≠
        (nb090AlphaDummy728 v u h) from (by
          unfold nb090AlphaDummy728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0749 v u h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy731 A),
        (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy749 A),
        (nb090AlphaDummy750 v u h)), ((nb090AlphaDummy747 A),
        (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy745 A),
        (nb090AlphaDummy746 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0754
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0755
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0752
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0753
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy737 A) from (by
          unfold
            nb090AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0758
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy738 v u h) from
        (by
          unfold
            nb090AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0759
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy735 A) from (by
          unfold
            nb090AlphaDummy735;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0756
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy736 v u h) from
        (by
          unfold
            nb090AlphaDummy736;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0757
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy731 A), (nb090AlphaDummy734 v u h)), ((nb090AlphaDummy730 A),
        (nb090AlphaDummy733 v u h)), ((nb090AlphaDummy729 A),
        (nb090AlphaDummy732 v u h)), ((nb090AlphaDummy727 A),
        (nb090AlphaDummy728 v u h)), ((nb090AlphaDummy723 A),
        (nb090AlphaDummy725 v u h)), ((nb090AlphaDummy724 A),
        (nb090AlphaDummy726 v u h)), ((nb090AlphaDummy749 A),
        (nb090AlphaDummy750 v u h)), ((nb090AlphaDummy747 A),
        (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A),
        (nb090AlphaDummy717 v u h)), ((nb090AlphaDummy745 A),
        (nb090AlphaDummy746 v u h)), ((nb090AlphaDummy719 A),
        (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A),
        (nb090AlphaDummy710 v u h)), ((nb090AlphaDummy712 A),
        (nb090AlphaDummy714 v u h)), ((nb090AlphaDummy711 A),
        (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠ (nb090AlphaDummy741 A) from (by
          unfold
            nb090AlphaDummy741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0762
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy742 v u h) from
        (by
          unfold
            nb090AlphaDummy742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0763
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy730 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0760
                    A)
                  0)))) (show (nb090AlphaDummy733 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0761
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy723
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy731 A) ≠ (nb090AlphaDummy743 A) from (by
          unfold
            nb090AlphaDummy743;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0766
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy744 v u h) from
        (by
          unfold
            nb090AlphaDummy744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0767
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy731 A) ≠
        (nb090AlphaDummy739 A) from (by
          unfold
            nb090AlphaDummy739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0764
                    A)
                  0)))) (show (nb090AlphaDummy734 v u h) ≠ (nb090AlphaDummy740 v u h) from
        (by
          unfold
            nb090AlphaDummy740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0765
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                (by
                                  unfold nb090AlphaDummy727;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                                (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h)
                                from (by
                                  unfold nb090AlphaDummy728;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                              ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                              ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                              ((nb090AlphaDummy749 A), (nb090AlphaDummy750 v u h)),
                              ((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)),
                              ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                              ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                              ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
                              ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                              ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                              ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                              ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                              ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                              ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                              ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                              ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                              ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from (by
                                unfold nb090AlphaDummy727;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                              (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h) from
                              (by
                                unfold nb090AlphaDummy728;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy723 A) ≠ (nb090AlphaDummy727 A) from
                                (by
                                  unfold nb090AlphaDummy727;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0748 A) 0)))) (show
                                (nb090AlphaDummy725 v u h) ≠ (nb090AlphaDummy728 v u h)
                                from (by
                                  unfold nb090AlphaDummy728;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0749 v u h)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy727 A), (nb090AlphaDummy728 v u h)),
                              ((nb090AlphaDummy723 A), (nb090AlphaDummy725 v u h)),
                              ((nb090AlphaDummy724 A), (nb090AlphaDummy726 v u h)),
                              ((nb090AlphaDummy749 A), (nb090AlphaDummy750 v u h)),
                              ((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)),
                              ((nb090AlphaDummy716 A), (nb090AlphaDummy718 v u h)),
                              ((nb090AlphaDummy715 A), (nb090AlphaDummy717 v u h)),
                              ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
                              ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)),
                              ((nb090AlphaDummy707 A), (nb090AlphaDummy708 v u h)),
                              ((nb090AlphaDummy709 A), (nb090AlphaDummy710 v u h)),
                              ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
                              ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)),
                              ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                              ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                              ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
                              ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
                              ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
                              ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
