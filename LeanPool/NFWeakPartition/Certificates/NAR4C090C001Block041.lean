/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block040

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part113`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0090`. -/
@[expose]
noncomputable def nb090SplitAlpha0090 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy705 A))
          (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy705 A))
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy706 v u h))
          (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy706 v u h))
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                        (freshVar_injective (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq
                                (Class.cab (nb090AlphaDummy707 A)
                                  (synWbr (Class.cv (nb090AlphaDummy041 A))
                                    (Class.cv (nb090AlphaDummy000 A))
                                    (Class.cv (nb090AlphaDummy707 A))))
                                (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv)
                          (by decide)) (freshVar_injective
                          (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
                                (Class.cab (nb090AlphaDummy708 v u h)
                                  (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                                    (Class.cv (nb090AlphaDummy708 v u h))))
                                (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv)
                          (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb090SplitAlpha0088 v u A h))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
          unfold
            nb090AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  1)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from
        (by
          unfold
            nb090AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy715 A) from (by
          unfold
            nb090AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from
        (by
          unfold
            nb090AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy745 A) from (by
          unfold
            nb090AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0772
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy746 v u h) from
        (by
          unfold
            nb090AlphaDummy746;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0773
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy719 A) from (by
          unfold
            nb090AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0769
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy720 v u h) from
        (by
          unfold
            nb090AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0771
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy043 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy708 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0089 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A), (nb090AlphaDummy717
        v u h)), ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A), (nb090AlphaDummy710
        v u h)), ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701
        v u h)), ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043
        v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
          unfold
            nb090AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  1)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from
        (by
          unfold
            nb090AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy715 A) from (by
          unfold
            nb090AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from
        (by
          unfold
            nb090AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy745 A) from (by
          unfold
            nb090AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0772
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy746 v u h) from
        (by
          unfold
            nb090AlphaDummy746;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0773
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy719 A) from (by
          unfold
            nb090AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0769
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy720 v u h) from
        (by
          unfold
            nb090AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0771
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy043 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy708 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0089 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A), (nb090AlphaDummy717
        v u h)), ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A), (nb090AlphaDummy710
        v u h)), ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701
        v u h)), ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043
        v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy707 A) from
                                    (by
                                      unfold nb090AlphaDummy707;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0786 A)
                                              0)))) (show h ≠ (nb090AlphaDummy708 v u h) from
                                    (by
                                      unfold nb090AlphaDummy708;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0789 v u h) 0))))
                                  (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
                                        (nb090AlphaDummy709 A) from (by
                                        unfold nb090AlphaDummy709;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0787 A)
                                                0))))
                                    (show h ≠ (nb090AlphaDummy710 v u h) from (by
                                        unfold nb090AlphaDummy710;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0790 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy712 A) from (by
                                          unfold nb090AlphaDummy712;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0788 A) 1))))
                                      (show h ≠ (nb090AlphaDummy714 v u h) from (by
                                          unfold nb090AlphaDummy714;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0791 v u h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy711 A) from (by
          unfold nb090AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0788 A) 0)))) (show h ≠ (nb090AlphaDummy713 v u h) from
        (by
          unfold nb090AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0791 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy700 A) from (by
          unfold nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780 A) 1)))) (show h ≠ (nb090AlphaDummy702 v u h) from
        (by
          unfold nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782 v u h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780 A) 0)))) (show h ≠ (nb090AlphaDummy701 v u h) from
        (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy705 A) from (by
          unfold nb090AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0784 A) 0)))) (show h ≠ (nb090AlphaDummy706 v u h) from
        (by
          unfold nb090AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0785 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781 A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778 A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779 v u
                    h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778 A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779 v
                    u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy709 A) ≠ (nb090AlphaDummy751 A) from
                                    (by
                                      unfold nb090AlphaDummy751;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0792 A)
                                              0)))) (show (nb090AlphaDummy710 v u h) ≠
                                      (nb090AlphaDummy752 v u h) from (by
                                      unfold nb090AlphaDummy752;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0793 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((synCfv (Class.cv (nb090AlphaDummy000 A))
                          (Class.cv (nb090AlphaDummy041 A)))).fv ∪
                      ((synCfv (Class.cv (nb090AlphaDummy000 A))
                          (Class.cv (nb090AlphaDummy042 A)))).fv) (by decide))
                  (freshVar_injective (((synCfv (Class.cv h)
                          (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪ ((synCfv (Class.cv h)
                          (Class.cv (nb090AlphaDummy044 v u h)))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy753 A) from (by
                              unfold nb090AlphaDummy753;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0794 A) 0)))) (show
                            (nb090AlphaDummy702 v u h) ≠ (nb090AlphaDummy755 v u h) from
                            (by
                              unfold nb090AlphaDummy755;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0795 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy754 A) from (by
                                unfold nb090AlphaDummy754;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0794 A) 1)))) (show
                              (nb090AlphaDummy702 v u h) ≠ (nb090AlphaDummy756 v u h) from
                              (by
                                unfold nb090AlphaDummy756;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy700 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090AlphaDummy702 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy760 A) from (by
          unfold nb090AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A) 1)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy763 v u h) from (by
          unfold nb090AlphaDummy763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy759 A) from (by
          unfold nb090AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A) 0)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy762 v u h) from (by
          unfold nb090AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy758 v u h) from
        (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy700 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy760
        A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from
                                      (by
                                        unfold nb090AlphaDummy757;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0796 A)
                                                0)))) (show (nb090AlphaDummy755 v u h) ≠
                                        (nb090AlphaDummy758 v u h) from (by
                                        unfold nb090AlphaDummy758;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0797 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy757 A), (nb090AlphaDummy758 v u h)),
                                    ((nb090AlphaDummy753 A), (nb090AlphaDummy755 v u h)),
                                    ((nb090AlphaDummy754 A), (nb090AlphaDummy756 v u h)),
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
                                    (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from
                                    (by
                                      unfold nb090AlphaDummy757;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0796 A)
                                              0)))) (show (nb090AlphaDummy755 v u h) ≠
                                      (nb090AlphaDummy758 v u h) from (by
                                      unfold nb090AlphaDummy758;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0797 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from
                                      (by
                                        unfold nb090AlphaDummy757;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0796 A)
                                                0)))) (show (nb090AlphaDummy755 v u h) ≠
                                        (nb090AlphaDummy758 v u h) from (by
                                        unfold nb090AlphaDummy758;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0797 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy757 A), (nb090AlphaDummy758 v u h)),
                                    ((nb090AlphaDummy753 A), (nb090AlphaDummy755 v u h)),
                                    ((nb090AlphaDummy754 A), (nb090AlphaDummy756 v u h)),
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
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                          (freshVar_injective (((Class.cab (nb090AlphaDummy709 A)
                                (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
                                    (synWbr (Class.cv (nb090AlphaDummy041 A))
                                      (Class.cv (nb090AlphaDummy000 A))
                                      (Class.cv (nb090AlphaDummy707 A))))
                                  (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
                                  (Class.cab (nb090AlphaDummy708 v u h)
                                    (synWbr (Class.cv (nb090AlphaDummy043 v u h))
                                      (Class.cv h) (Class.cv (nb090AlphaDummy708 v u h))))
                                  (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0088 v u A h))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
          unfold
            nb090AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  1)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from
        (by
          unfold
            nb090AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy715 A) from (by
          unfold
            nb090AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from
        (by
          unfold
            nb090AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy745 A) from (by
          unfold
            nb090AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0772
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy746 v u h) from
        (by
          unfold
            nb090AlphaDummy746;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0773
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy719 A) from (by
          unfold
            nb090AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0769
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy720 v u h) from
        (by
          unfold
            nb090AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0771
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy043 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy708 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0089 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A), (nb090AlphaDummy717
        v u h)), ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A), (nb090AlphaDummy710
        v u h)), ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701
        v u h)), ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043
        v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
          unfold
            nb090AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  1)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from
        (by
          unfold
            nb090AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy715 A) from (by
          unfold
            nb090AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0768
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from
        (by
          unfold
            nb090AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0770
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy745 A) from (by
          unfold
            nb090AlphaDummy745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0772
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy746 v u h) from
        (by
          unfold
            nb090AlphaDummy746;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0773
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy707 A) ≠
        (nb090AlphaDummy719 A) from (by
          unfold
            nb090AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0769
                    A)
                  0)))) (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy720 v u h) from
        (by
          unfold
            nb090AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0771
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy041 A))).fv ∪
        ((Class.cv (nb090AlphaDummy707 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy043 v u h))).fv ∪ ((Class.cv (nb090AlphaDummy708 v u h))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb090SplitAlpha0089 v u A h))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy747 A), (nb090AlphaDummy748 v u h)), ((nb090AlphaDummy716 A),
        (nb090AlphaDummy718 v u h)), ((nb090AlphaDummy715 A), (nb090AlphaDummy717
        v u h)), ((nb090AlphaDummy745 A), (nb090AlphaDummy746 v u h)),
        ((nb090AlphaDummy719 A), (nb090AlphaDummy720 v u h)), ((nb090AlphaDummy707 A),
        (nb090AlphaDummy708 v u h)), ((nb090AlphaDummy709 A), (nb090AlphaDummy710
        v u h)), ((nb090AlphaDummy712 A), (nb090AlphaDummy714 v u h)),
        ((nb090AlphaDummy711 A), (nb090AlphaDummy713 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A), (nb090AlphaDummy701
        v u h)), ((nb090AlphaDummy705 A), (nb090AlphaDummy706 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A), (nb090AlphaDummy043
        v u h)), ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A), (nb090AlphaDummy004
        v u A h))] (synCcompl (synCsn (synC0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy707 A) from
                                      (by
                                        unfold nb090AlphaDummy707;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0786 A)
                                                0))))
                                    (show h ≠ (nb090AlphaDummy708 v u h) from (by
                                        unfold nb090AlphaDummy708;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0789 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy709 A) from (by
                                          unfold nb090AlphaDummy709;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0787 A) 0))))
                                      (show h ≠ (nb090AlphaDummy710 v u h) from (by
                                          unfold nb090AlphaDummy710;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0790 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy712 A) from (by
          unfold nb090AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0788 A) 1)))) (show h ≠ (nb090AlphaDummy714 v u h) from
        (by
          unfold nb090AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0791 v u h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy711 A) from (by
          unfold nb090AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0788 A) 0)))) (show h ≠ (nb090AlphaDummy713 v u h) from
        (by
          unfold nb090AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0791 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy700 A) from (by
          unfold nb090AlphaDummy700;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780 A) 1)))) (show h ≠ (nb090AlphaDummy702 v u h) from
        (by
          unfold nb090AlphaDummy702;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0780 A) 0)))) (show h ≠ (nb090AlphaDummy701 v u h) from
        (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0782 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy705 A) from (by
          unfold nb090AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0784 A)
                  0)))) (show h ≠ (nb090AlphaDummy706 v u h) from (by
          unfold nb090AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0785 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0781 A)
                  0)))) (show h ≠ (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0783 v u
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy042 A) from (by
          unfold nb090AlphaDummy042;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778 A)
                  1)))) (show h ≠ (nb090AlphaDummy044 v u h) from (by
          unfold nb090AlphaDummy044;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779 v
                    u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy000 A) ≠
        (nb090AlphaDummy041 A) from (by
          unfold nb090AlphaDummy041;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0778
                    A)
                  0)))) (show h ≠ (nb090AlphaDummy043 v u h) from (by
          unfold nb090AlphaDummy043;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0779
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy709 A) ≠ (nb090AlphaDummy751 A) from
                                      (by
                                        unfold nb090AlphaDummy751;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0792 A)
                                                0)))) (show (nb090AlphaDummy710 v u h) ≠
                                        (nb090AlphaDummy752 v u h) from (by
                                        unfold nb090AlphaDummy752;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0793 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((synCfv (Class.cv (nb090AlphaDummy000 A))
                            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
                        ((synCfv (Class.cv (nb090AlphaDummy000 A))
                            (Class.cv (nb090AlphaDummy042 A)))).fv) (by decide))
                    (freshVar_injective (((synCfv (Class.cv h)
                            (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
                        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy753 A) from (by
                                unfold nb090AlphaDummy753;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0794 A) 0)))) (show
                              (nb090AlphaDummy702 v u h) ≠ (nb090AlphaDummy755 v u h) from
                              (by
                                unfold nb090AlphaDummy755;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy700 A) ≠ (nb090AlphaDummy754 A) from
                                (by
                                  unfold nb090AlphaDummy754;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0794 A) 1)))) (show
                                (nb090AlphaDummy702 v u h) ≠ (nb090AlphaDummy756 v u h)
                                from (by
                                  unfold nb090AlphaDummy756;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0795 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy700 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy702 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy760 A) from (by
          unfold nb090AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A) 1)))) (show (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy763 v u h) from (by
          unfold nb090AlphaDummy763;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy759 A) from (by
          unfold nb090AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0798 A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy762 v u h) from
        (by
          unfold nb090AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0799 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy753 A) ≠
        (nb090AlphaDummy757 A) from (by
          unfold nb090AlphaDummy757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0796 A)
                  0)))) (show (nb090AlphaDummy755 v u h) ≠ (nb090AlphaDummy758 v u h) from
        (by
          unfold nb090AlphaDummy758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0797 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy700 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0802
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0803
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0800
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0801
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠ (nb090AlphaDummy767 A) from (by
          unfold
            nb090AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0806
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy768 v u h) from
        (by
          unfold
            nb090AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0807
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy765 A) from (by
          unfold
            nb090AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0804
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy766 v u h) from
        (by
          unfold
            nb090AlphaDummy766;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0805
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy761 A), (nb090AlphaDummy764 v u h)), ((nb090AlphaDummy760 A),
        (nb090AlphaDummy763 v u h)), ((nb090AlphaDummy759 A),
        (nb090AlphaDummy762 v u h)), ((nb090AlphaDummy757 A),
        (nb090AlphaDummy758 v u h)), ((nb090AlphaDummy753 A),
        (nb090AlphaDummy755 v u h)), ((nb090AlphaDummy754 A),
        (nb090AlphaDummy756 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy705 A),
        (nb090AlphaDummy706 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy755 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy760
        A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠ (nb090AlphaDummy771 A) from (by
          unfold
            nb090AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0810
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy772 v u h) from
        (by
          unfold
            nb090AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0811
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy760 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0808
                    A)
                  0)))) (show (nb090AlphaDummy763 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0809
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy753
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy761
        A) ≠ (nb090AlphaDummy773 A) from (by
          unfold
            nb090AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0814
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy774 v u h) from
        (by
          unfold
            nb090AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0815
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy761 A) ≠
        (nb090AlphaDummy769 A) from (by
          unfold
            nb090AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0812
                    A)
                  0)))) (show (nb090AlphaDummy764 v u h) ≠ (nb090AlphaDummy770 v u h) from
        (by
          unfold
            nb090AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0813
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A)
                                        from (by
                                          unfold nb090AlphaDummy757;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0796 A) 0)))) (show
                                        (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
                                          unfold nb090AlphaDummy758;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0797 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy757 A), (nb090AlphaDummy758 v u h)),
                                      ((nb090AlphaDummy753 A),
                                        (nb090AlphaDummy755 v u h)),
                                      ((nb090AlphaDummy754 A),
                                        (nb090AlphaDummy756 v u h)),
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
                                      (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A) from
                                      (by
                                        unfold nb090AlphaDummy757;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0796 A)
                                                0)))) (show (nb090AlphaDummy755 v u h) ≠
                                        (nb090AlphaDummy758 v u h) from (by
                                        unfold nb090AlphaDummy758;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0797 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy753 A) ≠ (nb090AlphaDummy757 A)
                                        from (by
                                          unfold nb090AlphaDummy757;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0796 A) 0)))) (show
                                        (nb090AlphaDummy755 v u h) ≠
        (nb090AlphaDummy758 v u h) from (by
                                          unfold nb090AlphaDummy758;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0797 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy757 A), (nb090AlphaDummy758 v u h)),
                                      ((nb090AlphaDummy753 A),
                                        (nb090AlphaDummy755 v u h)),
                                      ((nb090AlphaDummy754 A),
                                        (nb090AlphaDummy756 v u h)),
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

/-! Certificates from `NAR4C090C001Part114`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0091`. -/
@[expose]
noncomputable def nb090SplitAlpha0091 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy791 A), (nb090AlphaDummy792 v u h)),
        ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
        ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
        ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
        ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
        ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
        ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
        ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
        ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
        ((nb090AlphaDummy703 A), (nb090AlphaDummy704 v u h)),
        ((nb090AlphaDummy042 A), (nb090AlphaDummy044 v u h)),
        ((nb090AlphaDummy041 A), (nb090AlphaDummy043 v u h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy791 A))
          (Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy791 A))
            (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCphi (Class.cv (nb090AlphaDummy786 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy792 v u h))
          (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy792 v u h))
            (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
                (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy786 A) from (by
                      unfold nb090AlphaDummy786;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
                  (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
                      unfold nb090AlphaDummy788;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy785 A) from (by
                        unfold nb090AlphaDummy785;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
                    (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy787 v u h) from (by
                        unfold nb090AlphaDummy787;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy791 A) from (by
                          unfold nb090AlphaDummy791;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0832 A) 0))))
                      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy792 v u h) from
                        (by
                          unfold nb090AlphaDummy792;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0833 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy789 A) from (by
                            unfold nb090AlphaDummy789;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0829 A) 0)))) (show
                          (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy790 v u h) from (by
                            unfold nb090AlphaDummy790;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0831 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy777 A) from (by
                              unfold nb090AlphaDummy777;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0822 A) 0)))) (show
                            (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy778 v u h) from
                            (by
                              unfold nb090AlphaDummy778;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0825 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy779 A) from (by
                                unfold nb090AlphaDummy779;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0823 A) 0)))) (show
                              (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy780 v u h) from
                              (by
                                unfold nb090AlphaDummy780;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0826 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy782 A) from
                                (by
                                  unfold nb090AlphaDummy782;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0824 A) 1)))) (show
                                (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy784 v u h)
                                from (by
                                  unfold nb090AlphaDummy784;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0827 v u h)
                                          1)))) (TAlphaVar.there (show
                                  (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy781 A) from (by
                                    unfold nb090AlphaDummy781;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0824 A)
                                            0)))) (show (nb090AlphaDummy044 v u h) ≠
                                    (nb090AlphaDummy783 v u h) from (by
                                    unfold nb090AlphaDummy783;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0827 v u h)
                                            0)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy700 A) from
                                    (by
                                      unfold nb090AlphaDummy700;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0816 A)
                                              1)))) (show (nb090AlphaDummy044 v u h) ≠
                                      (nb090AlphaDummy702 v u h) from (by
                                      unfold nb090AlphaDummy702;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0818 v u h) 1))))
                                  (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
                                        (nb090AlphaDummy699 A) from (by
                                        unfold nb090AlphaDummy699;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0816 A)
                                                0)))) (show (nb090AlphaDummy044 v u h) ≠
                                        (nb090AlphaDummy701 v u h) from (by
                                        unfold nb090AlphaDummy701;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0818 v u h) 0))))
                                    (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
        (nb090AlphaDummy775 A) from (by
                                          unfold nb090AlphaDummy775;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0820 A) 0)))) (show
                                        (nb090AlphaDummy044 v u h) ≠
        (nb090AlphaDummy776 v u h) from (by
                                          unfold nb090AlphaDummy776;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0821 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
        (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0817 A) 0)))) (show (nb090AlphaDummy044 v u h) ≠
        (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0819 v u h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy042 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
                      ((Class.cv (nb090AlphaDummy778 v u h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy793 A) from (by
                              unfold nb090AlphaDummy793;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0834 A) 0)))) (show
                            (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy795 v u h) from
                            (by
                              unfold nb090AlphaDummy795;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0835 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy794 A) from (by
                                unfold nb090AlphaDummy794;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0834 A) 1)))) (show
                              (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy796 v u h) from
                              (by
                                unfold nb090AlphaDummy796;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0835 v u h)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy786 A))).fv)
                            (by decide)) (freshVar_injective
                            (((Class.cv (nb090AlphaDummy788 v u h))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy800 A) from (by
          unfold nb090AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A) 1)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy803 v u h) from (by
          unfold nb090AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy799 A) from (by
          unfold nb090AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A) 0)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy802 v u h) from (by
          unfold nb090AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy797 A) from (by
          unfold nb090AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A)
                  0)))) (show (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
        (by
          unfold nb090AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy801 A), (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy791 A),
        (nb090AlphaDummy792 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy801 A), (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy791 A),
        (nb090AlphaDummy792 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy800
        A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801
        A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801
        A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                      (by
                                        unfold nb090AlphaDummy797;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0836 A)
                                                0)))) (show (nb090AlphaDummy795 v u h) ≠
                                        (nb090AlphaDummy798 v u h) from (by
                                        unfold nb090AlphaDummy798;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0837 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                                    ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                                    ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                                    ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                                    ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                                    ((nb090AlphaDummy791 A), (nb090AlphaDummy792 v u h)),
                                    ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                                    ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                                    ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                                    ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                                    ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                                    ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                                    ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                                    ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
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
                                    (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                    (by
                                      unfold nb090AlphaDummy797;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0836 A)
                                              0)))) (show (nb090AlphaDummy795 v u h) ≠
                                      (nb090AlphaDummy798 v u h) from (by
                                      unfold nb090AlphaDummy798;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0837 v u h) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                      (by
                                        unfold nb090AlphaDummy797;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0836 A)
                                                0)))) (show (nb090AlphaDummy795 v u h) ≠
                                        (nb090AlphaDummy798 v u h) from (by
                                        unfold nb090AlphaDummy798;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0837 v u h) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                                    ((nb090AlphaDummy793 A), (nb090AlphaDummy795 v u h)),
                                    ((nb090AlphaDummy794 A), (nb090AlphaDummy796 v u h)),
                                    ((nb090AlphaDummy786 A), (nb090AlphaDummy788 v u h)),
                                    ((nb090AlphaDummy785 A), (nb090AlphaDummy787 v u h)),
                                    ((nb090AlphaDummy791 A), (nb090AlphaDummy792 v u h)),
                                    ((nb090AlphaDummy789 A), (nb090AlphaDummy790 v u h)),
                                    ((nb090AlphaDummy777 A), (nb090AlphaDummy778 v u h)),
                                    ((nb090AlphaDummy779 A), (nb090AlphaDummy780 v u h)),
                                    ((nb090AlphaDummy782 A), (nb090AlphaDummy784 v u h)),
                                    ((nb090AlphaDummy781 A), (nb090AlphaDummy783 v u h)),
                                    ((nb090AlphaDummy700 A), (nb090AlphaDummy702 v u h)),
                                    ((nb090AlphaDummy699 A), (nb090AlphaDummy701 v u h)),
                                    ((nb090AlphaDummy775 A), (nb090AlphaDummy776 v u h)),
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
                    (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy786 A) from (by
                        unfold nb090AlphaDummy786;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
                    (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
                        unfold nb090AlphaDummy788;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
                    (TAlphaVar.there
                      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy785 A) from (by
                          unfold nb090AlphaDummy785;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
                      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy787 v u h) from
                        (by
                          unfold nb090AlphaDummy787;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy791 A) from (by
                            unfold nb090AlphaDummy791;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0832 A) 0)))) (show
                          (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy792 v u h) from (by
                            unfold nb090AlphaDummy792;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0833 v u h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy789 A) from (by
                              unfold nb090AlphaDummy789;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0829 A) 0)))) (show
                            (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy790 v u h) from
                            (by
                              unfold nb090AlphaDummy790;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0831 v u h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy777 A) from (by
                                unfold nb090AlphaDummy777;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0822 A) 0)))) (show
                              (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy778 v u h) from
                              (by
                                unfold nb090AlphaDummy778;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0825 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy779 A) from
                                (by
                                  unfold nb090AlphaDummy779;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0823 A) 0)))) (show
                                (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy780 v u h)
                                from (by
                                  unfold nb090AlphaDummy780;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0826 v u h)
                                          0)))) (TAlphaVar.there (show
                                  (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy782 A) from (by
                                    unfold nb090AlphaDummy782;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0824 A)
                                            1)))) (show (nb090AlphaDummy044 v u h) ≠
                                    (nb090AlphaDummy784 v u h) from (by
                                    unfold nb090AlphaDummy784;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0827 v u h)
                                            1)))) (TAlphaVar.there (show
                                    (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy781 A) from
                                    (by
                                      unfold nb090AlphaDummy781;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0824 A)
                                              0)))) (show (nb090AlphaDummy044 v u h) ≠
                                      (nb090AlphaDummy783 v u h) from (by
                                      unfold nb090AlphaDummy783;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb090_support_mem_0827 v u h) 0))))
                                  (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
                                        (nb090AlphaDummy700 A) from (by
                                        unfold nb090AlphaDummy700;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0816 A)
                                                1)))) (show (nb090AlphaDummy044 v u h) ≠
                                        (nb090AlphaDummy702 v u h) from (by
                                        unfold nb090AlphaDummy702;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0818 v u h) 1))))
                                    (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
        (nb090AlphaDummy699 A) from (by
                                          unfold nb090AlphaDummy699;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0816 A) 0)))) (show
                                        (nb090AlphaDummy044 v u h) ≠
        (nb090AlphaDummy701 v u h) from (by
                                          unfold nb090AlphaDummy701;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0818 v u h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy042 A) ≠
        (nb090AlphaDummy775 A) from (by
          unfold nb090AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0820 A) 0)))) (show (nb090AlphaDummy044 v u h) ≠
        (nb090AlphaDummy776 v u h) from (by
          unfold nb090AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0821 v u h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy703 A) from (by
          unfold nb090AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0817 A) 0)))) (show (nb090AlphaDummy044 v u h) ≠
        (nb090AlphaDummy704 v u h) from (by
          unfold nb090AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0819 v u h) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy042 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy777 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
                        ((Class.cv (nb090AlphaDummy778 v u h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy793 A) from (by
                                unfold nb090AlphaDummy793;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0834 A) 0)))) (show
                              (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy795 v u h) from
                              (by
                                unfold nb090AlphaDummy795;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0835 v u h)
                                        0)))) (TAlphaVar.there
                              (show (nb090AlphaDummy786 A) ≠ (nb090AlphaDummy794 A) from
                                (by
                                  unfold nb090AlphaDummy794;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0834 A) 1)))) (show
                                (nb090AlphaDummy788 v u h) ≠ (nb090AlphaDummy796 v u h)
                                from (by
                                  unfold nb090AlphaDummy796;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0835 v u h)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy786 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy788 v u h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy800 A) from (by
          unfold nb090AlphaDummy800;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A) 1)))) (show (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy803 v u h) from (by
          unfold nb090AlphaDummy803;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h)
                  1)))) (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy799 A) from (by
          unfold nb090AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0838 A)
                  0)))) (show (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy802 v u h) from
        (by
          unfold nb090AlphaDummy802;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0839 v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy793 A) ≠
        (nb090AlphaDummy797 A) from (by
          unfold nb090AlphaDummy797;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0836 A)
                  0)))) (show (nb090AlphaDummy795 v u h) ≠ (nb090AlphaDummy798 v u h) from
        (by
          unfold nb090AlphaDummy798;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0837 v u
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy801 A), (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy791 A),
        (nb090AlphaDummy792 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0842
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0843
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0840
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0841
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠ (nb090AlphaDummy807 A) from (by
          unfold
            nb090AlphaDummy807;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0846
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy808 v u h) from
        (by
          unfold
            nb090AlphaDummy808;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0847
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy805 A) from (by
          unfold
            nb090AlphaDummy805;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0844
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy806 v u h) from
        (by
          unfold
            nb090AlphaDummy806;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0845
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy801 A), (nb090AlphaDummy804 v u h)), ((nb090AlphaDummy800 A),
        (nb090AlphaDummy803 v u h)), ((nb090AlphaDummy799 A),
        (nb090AlphaDummy802 v u h)), ((nb090AlphaDummy797 A),
        (nb090AlphaDummy798 v u h)), ((nb090AlphaDummy793 A),
        (nb090AlphaDummy795 v u h)), ((nb090AlphaDummy794 A),
        (nb090AlphaDummy796 v u h)), ((nb090AlphaDummy786 A),
        (nb090AlphaDummy788 v u h)), ((nb090AlphaDummy785 A),
        (nb090AlphaDummy787 v u h)), ((nb090AlphaDummy791 A),
        (nb090AlphaDummy792 v u h)), ((nb090AlphaDummy789 A),
        (nb090AlphaDummy790 v u h)), ((nb090AlphaDummy777 A),
        (nb090AlphaDummy778 v u h)), ((nb090AlphaDummy779 A),
        (nb090AlphaDummy780 v u h)), ((nb090AlphaDummy782 A),
        (nb090AlphaDummy784 v u h)), ((nb090AlphaDummy781 A),
        (nb090AlphaDummy783 v u h)), ((nb090AlphaDummy700 A),
        (nb090AlphaDummy702 v u h)), ((nb090AlphaDummy699 A),
        (nb090AlphaDummy701 v u h)), ((nb090AlphaDummy775 A),
        (nb090AlphaDummy776 v u h)), ((nb090AlphaDummy703 A),
        (nb090AlphaDummy704 v u h)), ((nb090AlphaDummy042 A),
        (nb090AlphaDummy044 v u h)), ((nb090AlphaDummy041 A),
        (nb090AlphaDummy043 v u h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy795 v u
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy800
        A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠ (nb090AlphaDummy811 A) from (by
          unfold
            nb090AlphaDummy811;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0850
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy812 v u h) from
        (by
          unfold
            nb090AlphaDummy812;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0851
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy800 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0848
                    A)
                  0)))) (show (nb090AlphaDummy803 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0849
                    v u h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy793
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801
        A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy801
        A) ≠ (nb090AlphaDummy813 A) from (by
          unfold
            nb090AlphaDummy813;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0854
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy814 v u h) from
        (by
          unfold
            nb090AlphaDummy814;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0855
                    v u h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy801 A) ≠
        (nb090AlphaDummy809 A) from (by
          unfold
            nb090AlphaDummy809;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0852
                    A)
                  0)))) (show (nb090AlphaDummy804 v u h) ≠ (nb090AlphaDummy810 v u h) from
        (by
          unfold
            nb090AlphaDummy810;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0853
                    v u h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A)
                                        from (by
                                          unfold nb090AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0836 A) 0)))) (show
                                        (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy798 v u h) from (by
                                          unfold nb090AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0837 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                                      ((nb090AlphaDummy793 A),
                                        (nb090AlphaDummy795 v u h)),
                                      ((nb090AlphaDummy794 A),
                                        (nb090AlphaDummy796 v u h)),
                                      ((nb090AlphaDummy786 A),
                                        (nb090AlphaDummy788 v u h)),
                                      ((nb090AlphaDummy785 A),
                                        (nb090AlphaDummy787 v u h)),
                                      ((nb090AlphaDummy791 A),
                                        (nb090AlphaDummy792 v u h)),
                                      ((nb090AlphaDummy789 A),
                                        (nb090AlphaDummy790 v u h)),
                                      ((nb090AlphaDummy777 A),
                                        (nb090AlphaDummy778 v u h)),
                                      ((nb090AlphaDummy779 A),
                                        (nb090AlphaDummy780 v u h)),
                                      ((nb090AlphaDummy782 A),
                                        (nb090AlphaDummy784 v u h)),
                                      ((nb090AlphaDummy781 A),
                                        (nb090AlphaDummy783 v u h)),
                                      ((nb090AlphaDummy700 A),
                                        (nb090AlphaDummy702 v u h)),
                                      ((nb090AlphaDummy699 A),
                                        (nb090AlphaDummy701 v u h)),
                                      ((nb090AlphaDummy775 A),
                                        (nb090AlphaDummy776 v u h)),
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
                                      (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A) from
                                      (by
                                        unfold nb090AlphaDummy797;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0836 A)
                                                0)))) (show (nb090AlphaDummy795 v u h) ≠
                                        (nb090AlphaDummy798 v u h) from (by
                                        unfold nb090AlphaDummy798;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb090_support_mem_0837 v u h) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy793 A) ≠ (nb090AlphaDummy797 A)
                                        from (by
                                          unfold nb090AlphaDummy797;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0836 A) 0)))) (show
                                        (nb090AlphaDummy795 v u h) ≠
        (nb090AlphaDummy798 v u h) from (by
                                          unfold nb090AlphaDummy798;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0837 v u h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy797 A), (nb090AlphaDummy798 v u h)),
                                      ((nb090AlphaDummy793 A),
                                        (nb090AlphaDummy795 v u h)),
                                      ((nb090AlphaDummy794 A),
                                        (nb090AlphaDummy796 v u h)),
                                      ((nb090AlphaDummy786 A),
                                        (nb090AlphaDummy788 v u h)),
                                      ((nb090AlphaDummy785 A),
                                        (nb090AlphaDummy787 v u h)),
                                      ((nb090AlphaDummy791 A),
                                        (nb090AlphaDummy792 v u h)),
                                      ((nb090AlphaDummy789 A),
                                        (nb090AlphaDummy790 v u h)),
                                      ((nb090AlphaDummy777 A),
                                        (nb090AlphaDummy778 v u h)),
                                      ((nb090AlphaDummy779 A),
                                        (nb090AlphaDummy780 v u h)),
                                      ((nb090AlphaDummy782 A),
                                        (nb090AlphaDummy784 v u h)),
                                      ((nb090AlphaDummy781 A),
                                        (nb090AlphaDummy783 v u h)),
                                      ((nb090AlphaDummy700 A),
                                        (nb090AlphaDummy702 v u h)),
                                      ((nb090AlphaDummy699 A),
                                        (nb090AlphaDummy701 v u h)),
                                      ((nb090AlphaDummy775 A),
                                        (nb090AlphaDummy776 v u h)),
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
