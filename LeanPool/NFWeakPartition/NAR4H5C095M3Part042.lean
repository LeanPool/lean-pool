/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part041

/-! NF weak partition development: NAR4H5C095M3Part042. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0093`. -/
@[expose]
noncomputable def nb095SplitAlpha0093 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy753 D R S_cls E), (nb095AlphaDummy754 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy753 D R S_cls E))
          (Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy753 D R S_cls E))
            (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy754 x u D R S_cls f E))
          (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy754 x u D R S_cls f E))
            (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                  (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                      (nb095AlphaDummy748 D R S_cls E) from (by
                      unfold nb095AlphaDummy748;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1)))) (show
                    (nb095AlphaDummy006 x u D R S_cls f E) ≠
                      (nb095AlphaDummy750 x u D R S_cls f E) from (by
                      unfold nb095AlphaDummy750;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                        (nb095AlphaDummy747 D R S_cls E) from (by
                        unfold nb095AlphaDummy747;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy006 x u D R S_cls f E) ≠
                        (nb095AlphaDummy749 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy749;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095AlphaDummy004 D R S_cls E) ≠
                          (nb095AlphaDummy753 D R S_cls E) from (by
                          unfold nb095AlphaDummy753;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0794 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                          (nb095AlphaDummy754 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy754;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0795 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                            (nb095AlphaDummy751 D R S_cls E) from (by
                            unfold nb095AlphaDummy751;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0791 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                            (nb095AlphaDummy752 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy752;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0793 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                              (nb095AlphaDummy739 D R S_cls E) from (by
                              unfold nb095AlphaDummy739;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0784 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                              (nb095AlphaDummy740 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy740;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0787 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                (nb095AlphaDummy741 D R S_cls E) from (by
                                unfold nb095AlphaDummy741;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0785 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                (nb095AlphaDummy742 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy742;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0788 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                  (nb095AlphaDummy744 D R S_cls E) from (by
                                  unfold nb095AlphaDummy744;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0786 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy746 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy746;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0789 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                    (nb095AlphaDummy743 D R S_cls E) from (by
                                    unfold nb095AlphaDummy743;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0786 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                    (nb095AlphaDummy745 x u D R S_cls f E) from (by
                                    unfold nb095AlphaDummy745;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0789 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy004 D R S_cls E) ≠
                                      (nb095AlphaDummy662 D R S_cls E) from (by
                                      unfold nb095AlphaDummy662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0778 D R S_cls E) 1)))) (show
                                    (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy664 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0780 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy004 D R S_cls E) ≠
                                        (nb095AlphaDummy661 D R S_cls E) from (by
                                        unfold nb095AlphaDummy661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0778 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy663 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0780 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy004 D R S_cls E) ≠
        (nb095AlphaDummy737 D R S_cls E) from (by
                                          unfold nb095AlphaDummy737;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0782 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy006 x u D R S_cls f E) ≠
        (nb095AlphaDummy738 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy738;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0783 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0779 D R S_cls E)
                  0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
        (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0781 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                              (nb095AlphaDummy755 D R S_cls E) from (by
                              unfold nb095AlphaDummy755;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                              (nb095AlphaDummy757 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy757;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0797 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                                (nb095AlphaDummy756 D R S_cls E) from (by
                                unfold nb095AlphaDummy756;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                              (nb095AlphaDummy750 x u D R S_cls f E) ≠
                                (nb095AlphaDummy758 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy758;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy762 D R S_cls E) from (by
          unfold nb095AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy765 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy761 D R S_cls E) from (by
          unfold nb095AlphaDummy761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy764 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy759 D R S_cls E) from (by
          unfold nb095AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy763 D R S_cls E), (nb095AlphaDummy766 x u D R S_cls f E)),
        ((nb095AlphaDummy762 D R S_cls E), (nb095AlphaDummy765 x u D R S_cls f E)),
        ((nb095AlphaDummy761 D R S_cls E), (nb095AlphaDummy764 x u D R S_cls f E)),
        ((nb095AlphaDummy759 D R S_cls E), (nb095AlphaDummy760 x u D R S_cls f E)),
        ((nb095AlphaDummy755 D R S_cls E), (nb095AlphaDummy757 x u D R S_cls f E)),
        ((nb095AlphaDummy756 D R S_cls E), (nb095AlphaDummy758 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy753 D R S_cls E), (nb095AlphaDummy754 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762
        D R S_cls E) ≠ (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy763 D R S_cls E), (nb095AlphaDummy766 x u D R S_cls f E)),
        ((nb095AlphaDummy762 D R S_cls E), (nb095AlphaDummy765 x u D R S_cls f E)),
        ((nb095AlphaDummy761 D R S_cls E), (nb095AlphaDummy764 x u D R S_cls f E)),
        ((nb095AlphaDummy759 D R S_cls E), (nb095AlphaDummy760 x u D R S_cls f E)),
        ((nb095AlphaDummy755 D R S_cls E), (nb095AlphaDummy757 x u D R S_cls f E)),
        ((nb095AlphaDummy756 D R S_cls E), (nb095AlphaDummy758 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy753 D R S_cls E), (nb095AlphaDummy754 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762
        D R S_cls E) ≠ (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy774
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy774
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy776
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763
        D R S_cls E) ≠ (nb095AlphaDummy775 D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy776
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy755 D R S_cls E) ≠
                                        (nb095AlphaDummy759 D R S_cls E) from (by
                                        unfold nb095AlphaDummy759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy759 D R S_cls E),
                                      (nb095AlphaDummy760 x u D R S_cls f E)),
                                    ((nb095AlphaDummy755 D R S_cls E),
                                      (nb095AlphaDummy757 x u D R S_cls f E)),
                                    ((nb095AlphaDummy756 D R S_cls E),
                                      (nb095AlphaDummy758 x u D R S_cls f E)),
                                    ((nb095AlphaDummy748 D R S_cls E),
                                      (nb095AlphaDummy750 x u D R S_cls f E)),
                                    ((nb095AlphaDummy747 D R S_cls E),
                                      (nb095AlphaDummy749 x u D R S_cls f E)),
                                    ((nb095AlphaDummy753 D R S_cls E),
                                      (nb095AlphaDummy754 x u D R S_cls f E)),
                                    ((nb095AlphaDummy751 D R S_cls E),
                                      (nb095AlphaDummy752 x u D R S_cls f E)),
                                    ((nb095AlphaDummy739 D R S_cls E),
                                      (nb095AlphaDummy740 x u D R S_cls f E)),
                                    ((nb095AlphaDummy741 D R S_cls E),
                                      (nb095AlphaDummy742 x u D R S_cls f E)),
                                    ((nb095AlphaDummy744 D R S_cls E),
                                      (nb095AlphaDummy746 x u D R S_cls f E)),
                                    ((nb095AlphaDummy743 D R S_cls E),
                                      (nb095AlphaDummy745 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy737 D R S_cls E),
                                      (nb095AlphaDummy738 x u D R S_cls f E)),
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
                                    (nb095AlphaDummy755 D R S_cls E) ≠
                                      (nb095AlphaDummy759 D R S_cls E) from (by
                                      unfold nb095AlphaDummy759;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy760;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0799 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy755 D R S_cls E) ≠
                                        (nb095AlphaDummy759 D R S_cls E) from (by
                                        unfold nb095AlphaDummy759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy759 D R S_cls E),
                                      (nb095AlphaDummy760 x u D R S_cls f E)),
                                    ((nb095AlphaDummy755 D R S_cls E),
                                      (nb095AlphaDummy757 x u D R S_cls f E)),
                                    ((nb095AlphaDummy756 D R S_cls E),
                                      (nb095AlphaDummy758 x u D R S_cls f E)),
                                    ((nb095AlphaDummy748 D R S_cls E),
                                      (nb095AlphaDummy750 x u D R S_cls f E)),
                                    ((nb095AlphaDummy747 D R S_cls E),
                                      (nb095AlphaDummy749 x u D R S_cls f E)),
                                    ((nb095AlphaDummy753 D R S_cls E),
                                      (nb095AlphaDummy754 x u D R S_cls f E)),
                                    ((nb095AlphaDummy751 D R S_cls E),
                                      (nb095AlphaDummy752 x u D R S_cls f E)),
                                    ((nb095AlphaDummy739 D R S_cls E),
                                      (nb095AlphaDummy740 x u D R S_cls f E)),
                                    ((nb095AlphaDummy741 D R S_cls E),
                                      (nb095AlphaDummy742 x u D R S_cls f E)),
                                    ((nb095AlphaDummy744 D R S_cls E),
                                      (nb095AlphaDummy746 x u D R S_cls f E)),
                                    ((nb095AlphaDummy743 D R S_cls E),
                                      (nb095AlphaDummy745 x u D R S_cls f E)),
                                    ((nb095AlphaDummy662 D R S_cls E),
                                      (nb095AlphaDummy664 x u D R S_cls f E)),
                                    ((nb095AlphaDummy661 D R S_cls E),
                                      (nb095AlphaDummy663 x u D R S_cls f E)),
                                    ((nb095AlphaDummy737 D R S_cls E),
                                      (nb095AlphaDummy738 x u D R S_cls f E)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                        (nb095AlphaDummy748 D R S_cls E) from (by
                        unfold nb095AlphaDummy748;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy006 x u D R S_cls f E) ≠
                        (nb095AlphaDummy750 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy750;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095AlphaDummy004 D R S_cls E) ≠
                          (nb095AlphaDummy747 D R S_cls E) from (by
                          unfold nb095AlphaDummy747;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                          (nb095AlphaDummy749 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy749;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0792 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                            (nb095AlphaDummy753 D R S_cls E) from (by
                            unfold nb095AlphaDummy753;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0794 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                            (nb095AlphaDummy754 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy754;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0795 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                              (nb095AlphaDummy751 D R S_cls E) from (by
                              unfold nb095AlphaDummy751;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0791 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
                              (nb095AlphaDummy752 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy752;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0793 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                (nb095AlphaDummy739 D R S_cls E) from (by
                                unfold nb095AlphaDummy739;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0784 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                (nb095AlphaDummy740 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy740;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0787 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                  (nb095AlphaDummy741 D R S_cls E) from (by
                                  unfold nb095AlphaDummy741;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0785 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy742 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy742;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0788 x u D R S_cls f E) 0))))
                              (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
                                    (nb095AlphaDummy744 D R S_cls E) from (by
                                    unfold nb095AlphaDummy744;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0786 D R S_cls E) 1)))) (show
                                  (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                    (nb095AlphaDummy746 x u D R S_cls f E) from (by
                                    unfold nb095AlphaDummy746;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0789 x u D R S_cls f E)
                                            1)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy004 D R S_cls E) ≠
                                      (nb095AlphaDummy743 D R S_cls E) from (by
                                      unfold nb095AlphaDummy743;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0786 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                      (nb095AlphaDummy745 x u D R S_cls f E) from (by
                                      unfold nb095AlphaDummy745;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0789 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095AlphaDummy004 D R S_cls E) ≠
                                        (nb095AlphaDummy662 D R S_cls E) from (by
                                        unfold nb095AlphaDummy662;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0778 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy006 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy664 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy664;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0780 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy004 D R S_cls E) ≠
        (nb095AlphaDummy661 D R S_cls E) from (by
                                          unfold nb095AlphaDummy661;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0778 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy006 x u D R S_cls f E) ≠
        (nb095AlphaDummy663 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy663;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0780 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy737 D R S_cls E) from (by
          unfold nb095AlphaDummy737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0782 D R S_cls E)
                  0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
        (nb095AlphaDummy738 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0783 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy004 D R S_cls E) ≠
        (nb095AlphaDummy665 D R S_cls E) from (by
          unfold nb095AlphaDummy665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0779 D R S_cls E)
                  0)))) (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
        (nb095AlphaDummy666 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0781 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy748 D R S_cls E) ≠
                                (nb095AlphaDummy755 D R S_cls E) from (by
                                unfold nb095AlphaDummy755;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy750 x u D R S_cls f E) ≠
                                (nb095AlphaDummy757 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy757;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0797 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                                  (nb095AlphaDummy756 D R S_cls E) from (by
                                  unfold nb095AlphaDummy756;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                                (nb095AlphaDummy750 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy758 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy758;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy755 D R S_cls E) ≠ (nb095AlphaDummy762 D R S_cls E) from (by
          unfold nb095AlphaDummy762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy765 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy761 D R S_cls E) from (by
          unfold nb095AlphaDummy761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy764 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy759 D R S_cls E) from (by
          unfold nb095AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy763 D R S_cls E), (nb095AlphaDummy766 x u D R S_cls f E)),
        ((nb095AlphaDummy762 D R S_cls E), (nb095AlphaDummy765 x u D R S_cls f E)),
        ((nb095AlphaDummy761 D R S_cls E), (nb095AlphaDummy764 x u D R S_cls f E)),
        ((nb095AlphaDummy759 D R S_cls E), (nb095AlphaDummy760 x u D R S_cls f E)),
        ((nb095AlphaDummy755 D R S_cls E), (nb095AlphaDummy757 x u D R S_cls f E)),
        ((nb095AlphaDummy756 D R S_cls E), (nb095AlphaDummy758 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy753 D R S_cls E), (nb095AlphaDummy754 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762
        D R S_cls E) ≠ (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy770
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy768
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy763 D R S_cls E), (nb095AlphaDummy766 x u D R S_cls f E)),
        ((nb095AlphaDummy762 D R S_cls E), (nb095AlphaDummy765 x u D R S_cls f E)),
        ((nb095AlphaDummy761 D R S_cls E), (nb095AlphaDummy764 x u D R S_cls f E)),
        ((nb095AlphaDummy759 D R S_cls E), (nb095AlphaDummy760 x u D R S_cls f E)),
        ((nb095AlphaDummy755 D R S_cls E), (nb095AlphaDummy757 x u D R S_cls f E)),
        ((nb095AlphaDummy756 D R S_cls E), (nb095AlphaDummy758 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy753 D R S_cls E), (nb095AlphaDummy754 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762
        D R S_cls E) ≠ (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy774
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy774
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy776
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763
        D R S_cls E) ≠ (nb095AlphaDummy775 D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy776
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠ (nb095AlphaDummy772
        x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy759 D R S_cls E) from (by
                                          unfold nb095AlphaDummy759;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0798 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy760;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0799 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy759 D R S_cls E),
                                        (nb095AlphaDummy760 x u D R S_cls f E)),
                                      ((nb095AlphaDummy755 D R S_cls E),
                                        (nb095AlphaDummy757 x u D R S_cls f E)),
                                      ((nb095AlphaDummy756 D R S_cls E),
                                        (nb095AlphaDummy758 x u D R S_cls f E)),
                                      ((nb095AlphaDummy748 D R S_cls E),
                                        (nb095AlphaDummy750 x u D R S_cls f E)),
                                      ((nb095AlphaDummy747 D R S_cls E),
                                        (nb095AlphaDummy749 x u D R S_cls f E)),
                                      ((nb095AlphaDummy753 D R S_cls E),
                                        (nb095AlphaDummy754 x u D R S_cls f E)),
                                      ((nb095AlphaDummy751 D R S_cls E),
                                        (nb095AlphaDummy752 x u D R S_cls f E)),
                                      ((nb095AlphaDummy739 D R S_cls E),
                                        (nb095AlphaDummy740 x u D R S_cls f E)),
                                      ((nb095AlphaDummy741 D R S_cls E),
                                        (nb095AlphaDummy742 x u D R S_cls f E)),
                                      ((nb095AlphaDummy744 D R S_cls E),
                                        (nb095AlphaDummy746 x u D R S_cls f E)),
                                      ((nb095AlphaDummy743 D R S_cls E),
                                        (nb095AlphaDummy745 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy737 D R S_cls E),
                                        (nb095AlphaDummy738 x u D R S_cls f E)),
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
                                      (nb095AlphaDummy755 D R S_cls E) ≠
                                        (nb095AlphaDummy759 D R S_cls E) from (by
                                        unfold nb095AlphaDummy759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy759 D R S_cls E) from (by
                                          unfold nb095AlphaDummy759;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0798 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy760;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0799 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy759 D R S_cls E),
                                        (nb095AlphaDummy760 x u D R S_cls f E)),
                                      ((nb095AlphaDummy755 D R S_cls E),
                                        (nb095AlphaDummy757 x u D R S_cls f E)),
                                      ((nb095AlphaDummy756 D R S_cls E),
                                        (nb095AlphaDummy758 x u D R S_cls f E)),
                                      ((nb095AlphaDummy748 D R S_cls E),
                                        (nb095AlphaDummy750 x u D R S_cls f E)),
                                      ((nb095AlphaDummy747 D R S_cls E),
                                        (nb095AlphaDummy749 x u D R S_cls f E)),
                                      ((nb095AlphaDummy753 D R S_cls E),
                                        (nb095AlphaDummy754 x u D R S_cls f E)),
                                      ((nb095AlphaDummy751 D R S_cls E),
                                        (nb095AlphaDummy752 x u D R S_cls f E)),
                                      ((nb095AlphaDummy739 D R S_cls E),
                                        (nb095AlphaDummy740 x u D R S_cls f E)),
                                      ((nb095AlphaDummy741 D R S_cls E),
                                        (nb095AlphaDummy742 x u D R S_cls f E)),
                                      ((nb095AlphaDummy744 D R S_cls E),
                                        (nb095AlphaDummy746 x u D R S_cls f E)),
                                      ((nb095AlphaDummy743 D R S_cls E),
                                        (nb095AlphaDummy745 x u D R S_cls f E)),
                                      ((nb095AlphaDummy662 D R S_cls E),
                                        (nb095AlphaDummy664 x u D R S_cls f E)),
                                      ((nb095AlphaDummy661 D R S_cls E),
                                        (nb095AlphaDummy663 x u D R S_cls f E)),
                                      ((nb095AlphaDummy737 D R S_cls E),
                                        (nb095AlphaDummy738 x u D R S_cls f E)),
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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0094`. -/
@[expose]
noncomputable def nb095SplitAlpha0094 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy781 D R S_cls E), (nb095AlphaDummy782 x u D R S_cls f E)),
        ((nb095AlphaDummy779 D R S_cls E), (nb095AlphaDummy780 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy777 D R S_cls E), (nb095AlphaDummy778 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy781 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy781 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy782 x u D R S_cls f E))
          (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy782 x u D R S_cls f E))
            (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                      (nb095AlphaDummy755 D R S_cls E) from (by
                      unfold nb095AlphaDummy755;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                    (nb095AlphaDummy750 x u D R S_cls f E) ≠
                      (nb095AlphaDummy757 x u D R S_cls f E) from (by
                      unfold nb095AlphaDummy757;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                              0)))) (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                        (nb095AlphaDummy756 D R S_cls E) from (by
                        unfold nb095AlphaDummy756;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                      (nb095AlphaDummy750 x u D R S_cls f E) ≠
                        (nb095AlphaDummy758 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy758;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095AlphaDummy748 D R S_cls E) ≠
                          (nb095AlphaDummy781 D R S_cls E) from (by
                          unfold nb095AlphaDummy781;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0826 D R S_cls E)
                                  0)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                          (nb095AlphaDummy782 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy782;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0827 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                            (nb095AlphaDummy779 D R S_cls E) from (by
                            unfold nb095AlphaDummy779;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0824 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                            (nb095AlphaDummy780 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy780;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0825 x u D R S_cls f E) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy755 D R S_cls E) ≠
                                        (nb095AlphaDummy762 D R S_cls E) from (by
                                        unfold nb095AlphaDummy762;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0800 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                        (nb095AlphaDummy765 x u D R S_cls f E) from (by
                                        unfold nb095AlphaDummy765;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0801 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy761 D R S_cls E) from (by
                                          unfold nb095AlphaDummy761;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0800 D R S_cls E)
                                                  0)))) (show
                                        (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy764 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy764;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0801 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095AlphaDummy755 D R S_cls E) ≠ (nb095AlphaDummy759 D R S_cls E) from (by
          unfold nb095AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy763 D R S_cls E),
        (nb095AlphaDummy766 x u D R S_cls f E)), ((nb095AlphaDummy762 D R S_cls E),
        (nb095AlphaDummy765 x u D R S_cls f E)), ((nb095AlphaDummy761 D R S_cls E),
        (nb095AlphaDummy764 x u D R S_cls f E)), ((nb095AlphaDummy759 D R S_cls E),
        (nb095AlphaDummy760 x u D R S_cls f E)), ((nb095AlphaDummy755 D R S_cls E),
        (nb095AlphaDummy757 x u D R S_cls f E)), ((nb095AlphaDummy756 D R S_cls E),
        (nb095AlphaDummy758 x u D R S_cls f E)), ((nb095AlphaDummy781 D R S_cls E),
        (nb095AlphaDummy782 x u D R S_cls f E)), ((nb095AlphaDummy779 D R S_cls E),
        (nb095AlphaDummy780 x u D R S_cls f E)), ((nb095AlphaDummy748 D R S_cls E),
        (nb095AlphaDummy750 x u D R S_cls f E)), ((nb095AlphaDummy747 D R S_cls E),
        (nb095AlphaDummy749 x u D R S_cls f E)), ((nb095AlphaDummy777 D R S_cls E),
        (nb095AlphaDummy778 x u D R S_cls f E)), ((nb095AlphaDummy751 D R S_cls E),
        (nb095AlphaDummy752 x u D R S_cls f E)), ((nb095AlphaDummy739 D R S_cls E),
        (nb095AlphaDummy740 x u D R S_cls f E)), ((nb095AlphaDummy741 D R S_cls E),
        (nb095AlphaDummy742 x u D R S_cls f E)), ((nb095AlphaDummy744 D R S_cls E),
        (nb095AlphaDummy746 x u D R S_cls f E)), ((nb095AlphaDummy743 D R S_cls E),
        (nb095AlphaDummy745 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy737 D R S_cls E),
        (nb095AlphaDummy738 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
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
        (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy763 D R S_cls E),
        (nb095AlphaDummy766 x u D R S_cls f E)), ((nb095AlphaDummy762 D R S_cls E),
        (nb095AlphaDummy765 x u D R S_cls f E)), ((nb095AlphaDummy761 D R S_cls E),
        (nb095AlphaDummy764 x u D R S_cls f E)), ((nb095AlphaDummy759 D R S_cls E),
        (nb095AlphaDummy760 x u D R S_cls f E)), ((nb095AlphaDummy755 D R S_cls E),
        (nb095AlphaDummy757 x u D R S_cls f E)), ((nb095AlphaDummy756 D R S_cls E),
        (nb095AlphaDummy758 x u D R S_cls f E)), ((nb095AlphaDummy781 D R S_cls E),
        (nb095AlphaDummy782 x u D R S_cls f E)), ((nb095AlphaDummy779 D R S_cls E),
        (nb095AlphaDummy780 x u D R S_cls f E)), ((nb095AlphaDummy748 D R S_cls E),
        (nb095AlphaDummy750 x u D R S_cls f E)), ((nb095AlphaDummy747 D R S_cls E),
        (nb095AlphaDummy749 x u D R S_cls f E)), ((nb095AlphaDummy777 D R S_cls E),
        (nb095AlphaDummy778 x u D R S_cls f E)), ((nb095AlphaDummy751 D R S_cls E),
        (nb095AlphaDummy752 x u D R S_cls f E)), ((nb095AlphaDummy739 D R S_cls E),
        (nb095AlphaDummy740 x u D R S_cls f E)), ((nb095AlphaDummy741 D R S_cls E),
        (nb095AlphaDummy742 x u D R S_cls f E)), ((nb095AlphaDummy744 D R S_cls E),
        (nb095AlphaDummy746 x u D R S_cls f E)), ((nb095AlphaDummy743 D R S_cls E),
        (nb095AlphaDummy745 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy737 D R S_cls E),
        (nb095AlphaDummy738 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
        (nb095AlphaDummy666 x u D R S_cls f E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy774 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy774 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy776 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775 D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy776 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy755 D R S_cls E) ≠
                                (nb095AlphaDummy759 D R S_cls E) from (by
                                unfold nb095AlphaDummy759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy759 D R S_cls E),
                              (nb095AlphaDummy760 x u D R S_cls f E)),
                            ((nb095AlphaDummy755 D R S_cls E),
                              (nb095AlphaDummy757 x u D R S_cls f E)),
                            ((nb095AlphaDummy756 D R S_cls E),
                              (nb095AlphaDummy758 x u D R S_cls f E)),
                            ((nb095AlphaDummy781 D R S_cls E),
                              (nb095AlphaDummy782 x u D R S_cls f E)),
                            ((nb095AlphaDummy779 D R S_cls E),
                              (nb095AlphaDummy780 x u D R S_cls f E)),
                            ((nb095AlphaDummy748 D R S_cls E),
                              (nb095AlphaDummy750 x u D R S_cls f E)),
                            ((nb095AlphaDummy747 D R S_cls E),
                              (nb095AlphaDummy749 x u D R S_cls f E)),
                            ((nb095AlphaDummy777 D R S_cls E),
                              (nb095AlphaDummy778 x u D R S_cls f E)),
                            ((nb095AlphaDummy751 D R S_cls E),
                              (nb095AlphaDummy752 x u D R S_cls f E)),
                            ((nb095AlphaDummy739 D R S_cls E),
                              (nb095AlphaDummy740 x u D R S_cls f E)),
                            ((nb095AlphaDummy741 D R S_cls E),
                              (nb095AlphaDummy742 x u D R S_cls f E)),
                            ((nb095AlphaDummy744 D R S_cls E),
                              (nb095AlphaDummy746 x u D R S_cls f E)),
                            ((nb095AlphaDummy743 D R S_cls E),
                              (nb095AlphaDummy745 x u D R S_cls f E)),
                            ((nb095AlphaDummy662 D R S_cls E),
                              (nb095AlphaDummy664 x u D R S_cls f E)),
                            ((nb095AlphaDummy661 D R S_cls E),
                              (nb095AlphaDummy663 x u D R S_cls f E)),
                            ((nb095AlphaDummy737 D R S_cls E),
                              (nb095AlphaDummy738 x u D R S_cls f E)),
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
                        (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
                              (nb095AlphaDummy759 D R S_cls E) from (by
                              unfold nb095AlphaDummy759;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0798 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
                              (nb095AlphaDummy760 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy760;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy755 D R S_cls E) ≠
                                (nb095AlphaDummy759 D R S_cls E) from (by
                                unfold nb095AlphaDummy759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy759 D R S_cls E),
                              (nb095AlphaDummy760 x u D R S_cls f E)),
                            ((nb095AlphaDummy755 D R S_cls E),
                              (nb095AlphaDummy757 x u D R S_cls f E)),
                            ((nb095AlphaDummy756 D R S_cls E),
                              (nb095AlphaDummy758 x u D R S_cls f E)),
                            ((nb095AlphaDummy781 D R S_cls E),
                              (nb095AlphaDummy782 x u D R S_cls f E)),
                            ((nb095AlphaDummy779 D R S_cls E),
                              (nb095AlphaDummy780 x u D R S_cls f E)),
                            ((nb095AlphaDummy748 D R S_cls E),
                              (nb095AlphaDummy750 x u D R S_cls f E)),
                            ((nb095AlphaDummy747 D R S_cls E),
                              (nb095AlphaDummy749 x u D R S_cls f E)),
                            ((nb095AlphaDummy777 D R S_cls E),
                              (nb095AlphaDummy778 x u D R S_cls f E)),
                            ((nb095AlphaDummy751 D R S_cls E),
                              (nb095AlphaDummy752 x u D R S_cls f E)),
                            ((nb095AlphaDummy739 D R S_cls E),
                              (nb095AlphaDummy740 x u D R S_cls f E)),
                            ((nb095AlphaDummy741 D R S_cls E),
                              (nb095AlphaDummy742 x u D R S_cls f E)),
                            ((nb095AlphaDummy744 D R S_cls E),
                              (nb095AlphaDummy746 x u D R S_cls f E)),
                            ((nb095AlphaDummy743 D R S_cls E),
                              (nb095AlphaDummy745 x u D R S_cls f E)),
                            ((nb095AlphaDummy662 D R S_cls E),
                              (nb095AlphaDummy664 x u D R S_cls f E)),
                            ((nb095AlphaDummy661 D R S_cls E),
                              (nb095AlphaDummy663 x u D R S_cls f E)),
                            ((nb095AlphaDummy737 D R S_cls E),
                              (nb095AlphaDummy738 x u D R S_cls f E)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                        (nb095AlphaDummy755 D R S_cls E) from (by
                        unfold nb095AlphaDummy755;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                      (nb095AlphaDummy750 x u D R S_cls f E) ≠
                        (nb095AlphaDummy757 x u D R S_cls f E) from (by
                        unfold nb095AlphaDummy757;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095AlphaDummy748 D R S_cls E) ≠
                          (nb095AlphaDummy756 D R S_cls E) from (by
                          unfold nb095AlphaDummy756;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E)
                                  1)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                          (nb095AlphaDummy758 x u D R S_cls f E) from (by
                          unfold nb095AlphaDummy758;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                            (nb095AlphaDummy781 D R S_cls E) from (by
                            unfold nb095AlphaDummy781;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0826 D R S_cls E)
                                    0)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                            (nb095AlphaDummy782 x u D R S_cls f E) from (by
                            unfold nb095AlphaDummy782;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0827 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy748 D R S_cls E) ≠
                              (nb095AlphaDummy779 D R S_cls E) from (by
                              unfold nb095AlphaDummy779;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0824 D R S_cls E)
                                      0)))) (show (nb095AlphaDummy750 x u D R S_cls f E) ≠
                              (nb095AlphaDummy780 x u D R S_cls f E) from (by
                              unfold nb095AlphaDummy780;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0825 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy762 D R S_cls E) from (by
                                          unfold nb095AlphaDummy762;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0800 D R S_cls E)
                                                  1)))) (show
                                        (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy765 x u D R S_cls f E) from (by
                                          unfold nb095AlphaDummy765;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0801 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095AlphaDummy755 D R S_cls E) ≠ (nb095AlphaDummy761 D R S_cls E) from (by
          unfold nb095AlphaDummy761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy764 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy755 D R S_cls E) ≠
        (nb095AlphaDummy759 D R S_cls E) from (by
          unfold nb095AlphaDummy759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R S_cls E)
                  0)))) (show (nb095AlphaDummy757 x u D R S_cls f E) ≠
        (nb095AlphaDummy760 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy763 D R S_cls E),
        (nb095AlphaDummy766 x u D R S_cls f E)), ((nb095AlphaDummy762 D R S_cls E),
        (nb095AlphaDummy765 x u D R S_cls f E)), ((nb095AlphaDummy761 D R S_cls E),
        (nb095AlphaDummy764 x u D R S_cls f E)), ((nb095AlphaDummy759 D R S_cls E),
        (nb095AlphaDummy760 x u D R S_cls f E)), ((nb095AlphaDummy755 D R S_cls E),
        (nb095AlphaDummy757 x u D R S_cls f E)), ((nb095AlphaDummy756 D R S_cls E),
        (nb095AlphaDummy758 x u D R S_cls f E)), ((nb095AlphaDummy781 D R S_cls E),
        (nb095AlphaDummy782 x u D R S_cls f E)), ((nb095AlphaDummy779 D R S_cls E),
        (nb095AlphaDummy780 x u D R S_cls f E)), ((nb095AlphaDummy748 D R S_cls E),
        (nb095AlphaDummy750 x u D R S_cls f E)), ((nb095AlphaDummy747 D R S_cls E),
        (nb095AlphaDummy749 x u D R S_cls f E)), ((nb095AlphaDummy777 D R S_cls E),
        (nb095AlphaDummy778 x u D R S_cls f E)), ((nb095AlphaDummy751 D R S_cls E),
        (nb095AlphaDummy752 x u D R S_cls f E)), ((nb095AlphaDummy739 D R S_cls E),
        (nb095AlphaDummy740 x u D R S_cls f E)), ((nb095AlphaDummy741 D R S_cls E),
        (nb095AlphaDummy742 x u D R S_cls f E)), ((nb095AlphaDummy744 D R S_cls E),
        (nb095AlphaDummy746 x u D R S_cls f E)), ((nb095AlphaDummy743 D R S_cls E),
        (nb095AlphaDummy745 x u D R S_cls f E)), ((nb095AlphaDummy662 D R S_cls E),
        (nb095AlphaDummy664 x u D R S_cls f E)), ((nb095AlphaDummy661 D R S_cls E),
        (nb095AlphaDummy663 x u D R S_cls f E)), ((nb095AlphaDummy737 D R S_cls E),
        (nb095AlphaDummy738 x u D R S_cls f E)), ((nb095AlphaDummy665 D R S_cls E),
        (nb095AlphaDummy666 x u D R S_cls f E)), ((nb095AlphaDummy004 D R S_cls E),
        (nb095AlphaDummy006 x u D R S_cls f E)), ((nb095AlphaDummy003 D R S_cls E),
        (nb095AlphaDummy005 x u D R S_cls f E)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy769 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy769 D R S_cls E) from (by
          unfold
            nb095AlphaDummy769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy770 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy767 D R S_cls E) from (by
          unfold
            nb095AlphaDummy767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy768 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy763 D R S_cls E), (nb095AlphaDummy766 x u D R S_cls f E)),
        ((nb095AlphaDummy762 D R S_cls E), (nb095AlphaDummy765 x u D R S_cls f E)),
        ((nb095AlphaDummy761 D R S_cls E), (nb095AlphaDummy764 x u D R S_cls f E)),
        ((nb095AlphaDummy759 D R S_cls E), (nb095AlphaDummy760 x u D R S_cls f E)),
        ((nb095AlphaDummy755 D R S_cls E), (nb095AlphaDummy757 x u D R S_cls f E)),
        ((nb095AlphaDummy756 D R S_cls E), (nb095AlphaDummy758 x u D R S_cls f E)),
        ((nb095AlphaDummy781 D R S_cls E), (nb095AlphaDummy782 x u D R S_cls f E)),
        ((nb095AlphaDummy779 D R S_cls E), (nb095AlphaDummy780 x u D R S_cls f E)),
        ((nb095AlphaDummy748 D R S_cls E), (nb095AlphaDummy750 x u D R S_cls f E)),
        ((nb095AlphaDummy747 D R S_cls E), (nb095AlphaDummy749 x u D R S_cls f E)),
        ((nb095AlphaDummy777 D R S_cls E), (nb095AlphaDummy778 x u D R S_cls f E)),
        ((nb095AlphaDummy751 D R S_cls E), (nb095AlphaDummy752 x u D R S_cls f E)),
        ((nb095AlphaDummy739 D R S_cls E), (nb095AlphaDummy740 x u D R S_cls f E)),
        ((nb095AlphaDummy741 D R S_cls E), (nb095AlphaDummy742 x u D R S_cls f E)),
        ((nb095AlphaDummy744 D R S_cls E), (nb095AlphaDummy746 x u D R S_cls f E)),
        ((nb095AlphaDummy743 D R S_cls E), (nb095AlphaDummy745 x u D R S_cls f E)),
        ((nb095AlphaDummy662 D R S_cls E), (nb095AlphaDummy664 x u D R S_cls f E)),
        ((nb095AlphaDummy661 D R S_cls E), (nb095AlphaDummy663 x u D R S_cls f E)),
        ((nb095AlphaDummy737 D R S_cls E), (nb095AlphaDummy738 x u D R S_cls f E)),
        ((nb095AlphaDummy665 D R S_cls E), (nb095AlphaDummy666 x u D R S_cls f E)),
        ((nb095AlphaDummy004 D R S_cls E), (nb095AlphaDummy006 x u D R S_cls f E)),
        ((nb095AlphaDummy003 D R S_cls E), (nb095AlphaDummy005 x u D R S_cls f E)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy762 D R S_cls E) ≠ (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy774 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy773 D R S_cls E) from (by
          unfold
            nb095AlphaDummy773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy774 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy762 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy765 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy755
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy776 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy763 D R S_cls E) ≠ (nb095AlphaDummy775 D R S_cls E) from (by
          unfold
            nb095AlphaDummy775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy776 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy763 D R S_cls E) ≠
        (nb095AlphaDummy771 D R S_cls E) from (by
          unfold
            nb095AlphaDummy771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy766 x u D R S_cls f E) ≠
        (nb095AlphaDummy772 x u D R S_cls f E) from (by
          unfold
            nb095AlphaDummy772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy755 D R S_cls E) ≠
                                  (nb095AlphaDummy759 D R S_cls E) from (by
                                  unfold nb095AlphaDummy759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy759 D R S_cls E),
                                (nb095AlphaDummy760 x u D R S_cls f E)),
                              ((nb095AlphaDummy755 D R S_cls E),
                                (nb095AlphaDummy757 x u D R S_cls f E)),
                              ((nb095AlphaDummy756 D R S_cls E),
                                (nb095AlphaDummy758 x u D R S_cls f E)),
                              ((nb095AlphaDummy781 D R S_cls E),
                                (nb095AlphaDummy782 x u D R S_cls f E)),
                              ((nb095AlphaDummy779 D R S_cls E),
                                (nb095AlphaDummy780 x u D R S_cls f E)),
                              ((nb095AlphaDummy748 D R S_cls E),
                                (nb095AlphaDummy750 x u D R S_cls f E)),
                              ((nb095AlphaDummy747 D R S_cls E),
                                (nb095AlphaDummy749 x u D R S_cls f E)),
                              ((nb095AlphaDummy777 D R S_cls E),
                                (nb095AlphaDummy778 x u D R S_cls f E)),
                              ((nb095AlphaDummy751 D R S_cls E),
                                (nb095AlphaDummy752 x u D R S_cls f E)),
                              ((nb095AlphaDummy739 D R S_cls E),
                                (nb095AlphaDummy740 x u D R S_cls f E)),
                              ((nb095AlphaDummy741 D R S_cls E),
                                (nb095AlphaDummy742 x u D R S_cls f E)),
                              ((nb095AlphaDummy744 D R S_cls E),
                                (nb095AlphaDummy746 x u D R S_cls f E)),
                              ((nb095AlphaDummy743 D R S_cls E),
                                (nb095AlphaDummy745 x u D R S_cls f E)),
                              ((nb095AlphaDummy662 D R S_cls E),
                                (nb095AlphaDummy664 x u D R S_cls f E)),
                              ((nb095AlphaDummy661 D R S_cls E),
                                (nb095AlphaDummy663 x u D R S_cls f E)),
                              ((nb095AlphaDummy737 D R S_cls E),
                                (nb095AlphaDummy738 x u D R S_cls f E)),
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
                              (nb095AlphaDummy755 D R S_cls E) ≠
                                (nb095AlphaDummy759 D R S_cls E) from (by
                                unfold nb095AlphaDummy759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                unfold nb095AlphaDummy760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy755 D R S_cls E) ≠
                                  (nb095AlphaDummy759 D R S_cls E) from (by
                                  unfold nb095AlphaDummy759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                (nb095AlphaDummy757 x u D R S_cls f E) ≠
                                  (nb095AlphaDummy760 x u D R S_cls f E) from (by
                                  unfold nb095AlphaDummy760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy759 D R S_cls E),
                                (nb095AlphaDummy760 x u D R S_cls f E)),
                              ((nb095AlphaDummy755 D R S_cls E),
                                (nb095AlphaDummy757 x u D R S_cls f E)),
                              ((nb095AlphaDummy756 D R S_cls E),
                                (nb095AlphaDummy758 x u D R S_cls f E)),
                              ((nb095AlphaDummy781 D R S_cls E),
                                (nb095AlphaDummy782 x u D R S_cls f E)),
                              ((nb095AlphaDummy779 D R S_cls E),
                                (nb095AlphaDummy780 x u D R S_cls f E)),
                              ((nb095AlphaDummy748 D R S_cls E),
                                (nb095AlphaDummy750 x u D R S_cls f E)),
                              ((nb095AlphaDummy747 D R S_cls E),
                                (nb095AlphaDummy749 x u D R S_cls f E)),
                              ((nb095AlphaDummy777 D R S_cls E),
                                (nb095AlphaDummy778 x u D R S_cls f E)),
                              ((nb095AlphaDummy751 D R S_cls E),
                                (nb095AlphaDummy752 x u D R S_cls f E)),
                              ((nb095AlphaDummy739 D R S_cls E),
                                (nb095AlphaDummy740 x u D R S_cls f E)),
                              ((nb095AlphaDummy741 D R S_cls E),
                                (nb095AlphaDummy742 x u D R S_cls f E)),
                              ((nb095AlphaDummy744 D R S_cls E),
                                (nb095AlphaDummy746 x u D R S_cls f E)),
                              ((nb095AlphaDummy743 D R S_cls E),
                                (nb095AlphaDummy745 x u D R S_cls f E)),
                              ((nb095AlphaDummy662 D R S_cls E),
                                (nb095AlphaDummy664 x u D R S_cls f E)),
                              ((nb095AlphaDummy661 D R S_cls E),
                                (nb095AlphaDummy663 x u D R S_cls f E)),
                              ((nb095AlphaDummy737 D R S_cls E),
                                (nb095AlphaDummy738 x u D R S_cls f E)),
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
