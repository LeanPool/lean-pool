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

@[expose]
noncomputable def nb095_split_alpha_0093 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_753 D R S_cls E), (nb095_alpha_dummy_754 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_753 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_753 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_754 x u D R S_cls f E))
          (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_754 x u D R S_cls f E))
            (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                      (nb095_alpha_dummy_748 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_748;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1)))) (show
                    (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                      (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
                      unfold nb095_alpha_dummy_750;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                              1)))) (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                        (nb095_alpha_dummy_747 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_747;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_749;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_004 D R S_cls E) ≠
                          (nb095_alpha_dummy_753 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_753;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0794 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_754 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_754;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0795 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                            (nb095_alpha_dummy_751 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_751;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0791 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_752 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_752;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0793 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                              (nb095_alpha_dummy_739 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_739;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0784 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_740 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_740;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0787 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                (nb095_alpha_dummy_741 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_741;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0785 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_742 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_742;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0788 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                  (nb095_alpha_dummy_744 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_744;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0786 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_746 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_746;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0789 x u D R S_cls f E) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                    (nb095_alpha_dummy_743 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_743;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0786 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                    (nb095_alpha_dummy_745 x u D R S_cls f E) from (by
                                    unfold nb095_alpha_dummy_745;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0789 x u D R S_cls f E)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_004 D R S_cls E) ≠
                                      (nb095_alpha_dummy_662 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_662;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0778 D R S_cls E) 1)))) (show
                                    (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_664;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0780 x u D R S_cls f E)
                                              1)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_004 D R S_cls E) ≠
                                        (nb095_alpha_dummy_661 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_661;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0778 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_663;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0780 x u D R S_cls f E)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_004 D R S_cls E) ≠
        (nb095_alpha_dummy_737 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_737;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0782 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_738 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_738;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0783 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0779 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0781 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                              (nb095_alpha_dummy_755 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_755;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_757 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_757;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0797 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                                (nb095_alpha_dummy_756 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_756;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_758 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_758;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_762 D R S_cls E) from (by
          unfold nb095_alpha_dummy_762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_765 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_761 D R S_cls E) from (by
          unfold nb095_alpha_dummy_761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_764 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_759 D R S_cls E) from (by
          unfold nb095_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_763 D R S_cls E), (nb095_alpha_dummy_766 x u D R S_cls f E)),
        ((nb095_alpha_dummy_762 D R S_cls E), (nb095_alpha_dummy_765 x u D R S_cls f E)),
        ((nb095_alpha_dummy_761 D R S_cls E), (nb095_alpha_dummy_764 x u D R S_cls f E)),
        ((nb095_alpha_dummy_759 D R S_cls E), (nb095_alpha_dummy_760 x u D R S_cls f E)),
        ((nb095_alpha_dummy_755 D R S_cls E), (nb095_alpha_dummy_757 x u D R S_cls f E)),
        ((nb095_alpha_dummy_756 D R S_cls E), (nb095_alpha_dummy_758 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_753 D R S_cls E), (nb095_alpha_dummy_754 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762
        D R S_cls E) ≠ (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_763 D R S_cls E), (nb095_alpha_dummy_766 x u D R S_cls f E)),
        ((nb095_alpha_dummy_762 D R S_cls E), (nb095_alpha_dummy_765 x u D R S_cls f E)),
        ((nb095_alpha_dummy_761 D R S_cls E), (nb095_alpha_dummy_764 x u D R S_cls f E)),
        ((nb095_alpha_dummy_759 D R S_cls E), (nb095_alpha_dummy_760 x u D R S_cls f E)),
        ((nb095_alpha_dummy_755 D R S_cls E), (nb095_alpha_dummy_757 x u D R S_cls f E)),
        ((nb095_alpha_dummy_756 D R S_cls E), (nb095_alpha_dummy_758 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_753 D R S_cls E), (nb095_alpha_dummy_754 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762
        D R S_cls E) ≠ (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_774
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_774
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_776
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763
        D R S_cls E) ≠ (nb095_alpha_dummy_775 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_776
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
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
                                      (nb095_alpha_dummy_755 D R S_cls E) ≠
                                        (nb095_alpha_dummy_759 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_759 D R S_cls E),
                                      (nb095_alpha_dummy_760 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_755 D R S_cls E),
                                      (nb095_alpha_dummy_757 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_756 D R S_cls E),
                                      (nb095_alpha_dummy_758 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_748 D R S_cls E),
                                      (nb095_alpha_dummy_750 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_747 D R S_cls E),
                                      (nb095_alpha_dummy_749 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_753 D R S_cls E),
                                      (nb095_alpha_dummy_754 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_751 D R S_cls E),
                                      (nb095_alpha_dummy_752 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_739 D R S_cls E),
                                      (nb095_alpha_dummy_740 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_741 D R S_cls E),
                                      (nb095_alpha_dummy_742 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_744 D R S_cls E),
                                      (nb095_alpha_dummy_746 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_743 D R S_cls E),
                                      (nb095_alpha_dummy_745 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_737 D R S_cls E),
                                      (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                                    (nb095_alpha_dummy_755 D R S_cls E) ≠
                                      (nb095_alpha_dummy_759 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_759;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_760;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0799 x u D R S_cls f E)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_755 D R S_cls E) ≠
                                        (nb095_alpha_dummy_759 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_759 D R S_cls E),
                                      (nb095_alpha_dummy_760 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_755 D R S_cls E),
                                      (nb095_alpha_dummy_757 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_756 D R S_cls E),
                                      (nb095_alpha_dummy_758 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_748 D R S_cls E),
                                      (nb095_alpha_dummy_750 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_747 D R S_cls E),
                                      (nb095_alpha_dummy_749 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_753 D R S_cls E),
                                      (nb095_alpha_dummy_754 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_751 D R S_cls E),
                                      (nb095_alpha_dummy_752 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_739 D R S_cls E),
                                      (nb095_alpha_dummy_740 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_741 D R S_cls E),
                                      (nb095_alpha_dummy_742 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_744 D R S_cls E),
                                      (nb095_alpha_dummy_746 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_743 D R S_cls E),
                                      (nb095_alpha_dummy_745 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_662 D R S_cls E),
                                      (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_661 D R S_cls E),
                                      (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                    ((nb095_alpha_dummy_737 D R S_cls E),
                                      (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                        (nb095_alpha_dummy_748 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_748;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_750;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_004 D R S_cls E) ≠
                          (nb095_alpha_dummy_747 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_747;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_749;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0792 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                            (nb095_alpha_dummy_753 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_753;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0794 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_754 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_754;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0795 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                              (nb095_alpha_dummy_751 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_751;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0791 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_752 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_752;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0793 x u D R S_cls f E) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                (nb095_alpha_dummy_739 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_739;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0784 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_740 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_740;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0787 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                  (nb095_alpha_dummy_741 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_741;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0785 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_742 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_742;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0788 x u D R S_cls f E) 0))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
                                    (nb095_alpha_dummy_744 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_744;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0786 D R S_cls E) 1)))) (show
                                  (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                    (nb095_alpha_dummy_746 x u D R S_cls f E) from (by
                                    unfold nb095_alpha_dummy_746;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0789 x u D R S_cls f E)
                                            1)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_004 D R S_cls E) ≠
                                      (nb095_alpha_dummy_743 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_743;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0786 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                      (nb095_alpha_dummy_745 x u D R S_cls f E) from (by
                                      unfold nb095_alpha_dummy_745;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0789 x u D R S_cls f E)
                                              0)))) (TAlphaVar.there (show
                                      (nb095_alpha_dummy_004 D R S_cls E) ≠
                                        (nb095_alpha_dummy_662 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_662;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0778 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_664;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0780 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_004 D R S_cls E) ≠
        (nb095_alpha_dummy_661 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_661;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0778 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_663;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0780 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_737 D R S_cls E) from (by
          unfold nb095_alpha_dummy_737;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0782 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_738 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_738;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0783 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_004 D R S_cls E) ≠
        (nb095_alpha_dummy_665 D R S_cls E) from (by
          unfold nb095_alpha_dummy_665;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0779 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_666 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_666;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0781 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_748 D R S_cls E) ≠
                                (nb095_alpha_dummy_755 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_755;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_757 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_757;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0797 x u D R S_cls f E) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                                  (nb095_alpha_dummy_756 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_756;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_758 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_758;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_755 D R S_cls E) ≠ (nb095_alpha_dummy_762 D R S_cls E) from (by
          unfold nb095_alpha_dummy_762;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_765 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_765;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R
                    S_cls f E)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_761 D R S_cls E) from (by
          unfold nb095_alpha_dummy_761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_764 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D
                    R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_759 D R S_cls E) from (by
          unfold nb095_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u
                    D R S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_763 D R S_cls E), (nb095_alpha_dummy_766 x u D R S_cls f E)),
        ((nb095_alpha_dummy_762 D R S_cls E), (nb095_alpha_dummy_765 x u D R S_cls f E)),
        ((nb095_alpha_dummy_761 D R S_cls E), (nb095_alpha_dummy_764 x u D R S_cls f E)),
        ((nb095_alpha_dummy_759 D R S_cls E), (nb095_alpha_dummy_760 x u D R S_cls f E)),
        ((nb095_alpha_dummy_755 D R S_cls E), (nb095_alpha_dummy_757 x u D R S_cls f E)),
        ((nb095_alpha_dummy_756 D R S_cls E), (nb095_alpha_dummy_758 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_753 D R S_cls E), (nb095_alpha_dummy_754 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762
        D R S_cls E) ≠ (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_770
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_768
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_763 D R S_cls E), (nb095_alpha_dummy_766 x u D R S_cls f E)),
        ((nb095_alpha_dummy_762 D R S_cls E), (nb095_alpha_dummy_765 x u D R S_cls f E)),
        ((nb095_alpha_dummy_761 D R S_cls E), (nb095_alpha_dummy_764 x u D R S_cls f E)),
        ((nb095_alpha_dummy_759 D R S_cls E), (nb095_alpha_dummy_760 x u D R S_cls f E)),
        ((nb095_alpha_dummy_755 D R S_cls E), (nb095_alpha_dummy_757 x u D R S_cls f E)),
        ((nb095_alpha_dummy_756 D R S_cls E), (nb095_alpha_dummy_758 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_753 D R S_cls E), (nb095_alpha_dummy_754 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762
        D R S_cls E) ≠ (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_774
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_774
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D
                    R
                    S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_776
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763
        D R S_cls E) ≠ (nb095_alpha_dummy_775 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_776
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R
                    S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠ (nb095_alpha_dummy_772
        x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
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
                                        (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_759 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_759;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0798 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_760;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0799 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_759 D R S_cls E),
                                        (nb095_alpha_dummy_760 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_755 D R S_cls E),
                                        (nb095_alpha_dummy_757 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_756 D R S_cls E),
                                        (nb095_alpha_dummy_758 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_748 D R S_cls E),
                                        (nb095_alpha_dummy_750 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_747 D R S_cls E),
                                        (nb095_alpha_dummy_749 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_753 D R S_cls E),
                                        (nb095_alpha_dummy_754 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_751 D R S_cls E),
                                        (nb095_alpha_dummy_752 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_739 D R S_cls E),
                                        (nb095_alpha_dummy_740 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_741 D R S_cls E),
                                        (nb095_alpha_dummy_742 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_744 D R S_cls E),
                                        (nb095_alpha_dummy_746 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_743 D R S_cls E),
                                        (nb095_alpha_dummy_745 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_737 D R S_cls E),
                                        (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                                      (nb095_alpha_dummy_755 D R S_cls E) ≠
                                        (nb095_alpha_dummy_759 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_759;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_760;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0799 x u D R S_cls f E)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_759 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_759;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0798 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_760;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0799 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_759 D R S_cls E),
                                        (nb095_alpha_dummy_760 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_755 D R S_cls E),
                                        (nb095_alpha_dummy_757 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_756 D R S_cls E),
                                        (nb095_alpha_dummy_758 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_748 D R S_cls E),
                                        (nb095_alpha_dummy_750 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_747 D R S_cls E),
                                        (nb095_alpha_dummy_749 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_753 D R S_cls E),
                                        (nb095_alpha_dummy_754 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_751 D R S_cls E),
                                        (nb095_alpha_dummy_752 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_739 D R S_cls E),
                                        (nb095_alpha_dummy_740 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_741 D R S_cls E),
                                        (nb095_alpha_dummy_742 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_744 D R S_cls E),
                                        (nb095_alpha_dummy_746 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_743 D R S_cls E),
                                        (nb095_alpha_dummy_745 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_662 D R S_cls E),
                                        (nb095_alpha_dummy_664 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_661 D R S_cls E),
                                        (nb095_alpha_dummy_663 x u D R S_cls f E)),
                                      ((nb095_alpha_dummy_737 D R S_cls E),
                                        (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
noncomputable def nb095_split_alpha_0094 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_781 D R S_cls E), (nb095_alpha_dummy_782 x u D R S_cls f E)),
        ((nb095_alpha_dummy_779 D R S_cls E), (nb095_alpha_dummy_780 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_777 D R S_cls E), (nb095_alpha_dummy_778 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_781 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_781 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_782 x u D R S_cls f E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_782 x u D R S_cls f E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                      (nb095_alpha_dummy_755 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_755;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                    (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                      (nb095_alpha_dummy_757 x u D R S_cls f E) from (by
                      unfold nb095_alpha_dummy_757;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                              0)))) (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                        (nb095_alpha_dummy_756 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_756;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_758 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_758;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                                1)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_748 D R S_cls E) ≠
                          (nb095_alpha_dummy_781 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_781;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0826 D R S_cls E)
                                  0)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_782 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_782;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0827 x u D R S_cls f E) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                            (nb095_alpha_dummy_779 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_779;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0824 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_780 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_780;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0825 x u D R S_cls f E) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) (by decide))
                  (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_755 D R S_cls E) ≠
                                        (nb095_alpha_dummy_762 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_762;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0800 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                        (nb095_alpha_dummy_765 x u D R S_cls f E) from (by
                                        unfold nb095_alpha_dummy_765;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0801 x u D R S_cls f E)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_761 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_761;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0800 D R S_cls E)
                                                  0)))) (show
                                        (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_764 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_764;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0801 x u D R S_cls f
                                                    E)
                                                  0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_755 D R S_cls E) ≠ (nb095_alpha_dummy_759 D R S_cls E) from (by
          unfold nb095_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_763 D R S_cls E),
        (nb095_alpha_dummy_766 x u D R S_cls f E)), ((nb095_alpha_dummy_762 D R S_cls E),
        (nb095_alpha_dummy_765 x u D R S_cls f E)), ((nb095_alpha_dummy_761 D R S_cls E),
        (nb095_alpha_dummy_764 x u D R S_cls f E)), ((nb095_alpha_dummy_759 D R S_cls E),
        (nb095_alpha_dummy_760 x u D R S_cls f E)), ((nb095_alpha_dummy_755 D R S_cls E),
        (nb095_alpha_dummy_757 x u D R S_cls f E)), ((nb095_alpha_dummy_756 D R S_cls E),
        (nb095_alpha_dummy_758 x u D R S_cls f E)), ((nb095_alpha_dummy_781 D R S_cls E),
        (nb095_alpha_dummy_782 x u D R S_cls f E)), ((nb095_alpha_dummy_779 D R S_cls E),
        (nb095_alpha_dummy_780 x u D R S_cls f E)), ((nb095_alpha_dummy_748 D R S_cls E),
        (nb095_alpha_dummy_750 x u D R S_cls f E)), ((nb095_alpha_dummy_747 D R S_cls E),
        (nb095_alpha_dummy_749 x u D R S_cls f E)), ((nb095_alpha_dummy_777 D R S_cls E),
        (nb095_alpha_dummy_778 x u D R S_cls f E)), ((nb095_alpha_dummy_751 D R S_cls E),
        (nb095_alpha_dummy_752 x u D R S_cls f E)), ((nb095_alpha_dummy_739 D R S_cls E),
        (nb095_alpha_dummy_740 x u D R S_cls f E)), ((nb095_alpha_dummy_741 D R S_cls E),
        (nb095_alpha_dummy_742 x u D R S_cls f E)), ((nb095_alpha_dummy_744 D R S_cls E),
        (nb095_alpha_dummy_746 x u D R S_cls f E)), ((nb095_alpha_dummy_743 D R S_cls E),
        (nb095_alpha_dummy_745 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_737 D R S_cls E),
        (nb095_alpha_dummy_738 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
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
        (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_763 D R S_cls E),
        (nb095_alpha_dummy_766 x u D R S_cls f E)), ((nb095_alpha_dummy_762 D R S_cls E),
        (nb095_alpha_dummy_765 x u D R S_cls f E)), ((nb095_alpha_dummy_761 D R S_cls E),
        (nb095_alpha_dummy_764 x u D R S_cls f E)), ((nb095_alpha_dummy_759 D R S_cls E),
        (nb095_alpha_dummy_760 x u D R S_cls f E)), ((nb095_alpha_dummy_755 D R S_cls E),
        (nb095_alpha_dummy_757 x u D R S_cls f E)), ((nb095_alpha_dummy_756 D R S_cls E),
        (nb095_alpha_dummy_758 x u D R S_cls f E)), ((nb095_alpha_dummy_781 D R S_cls E),
        (nb095_alpha_dummy_782 x u D R S_cls f E)), ((nb095_alpha_dummy_779 D R S_cls E),
        (nb095_alpha_dummy_780 x u D R S_cls f E)), ((nb095_alpha_dummy_748 D R S_cls E),
        (nb095_alpha_dummy_750 x u D R S_cls f E)), ((nb095_alpha_dummy_747 D R S_cls E),
        (nb095_alpha_dummy_749 x u D R S_cls f E)), ((nb095_alpha_dummy_777 D R S_cls E),
        (nb095_alpha_dummy_778 x u D R S_cls f E)), ((nb095_alpha_dummy_751 D R S_cls E),
        (nb095_alpha_dummy_752 x u D R S_cls f E)), ((nb095_alpha_dummy_739 D R S_cls E),
        (nb095_alpha_dummy_740 x u D R S_cls f E)), ((nb095_alpha_dummy_741 D R S_cls E),
        (nb095_alpha_dummy_742 x u D R S_cls f E)), ((nb095_alpha_dummy_744 D R S_cls E),
        (nb095_alpha_dummy_746 x u D R S_cls f E)), ((nb095_alpha_dummy_743 D R S_cls E),
        (nb095_alpha_dummy_745 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_737 D R S_cls E),
        (nb095_alpha_dummy_738 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
        (nb095_alpha_dummy_666 x u D R S_cls f E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_774 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_774 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_776 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_776 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_755 D R S_cls E) ≠
                                (nb095_alpha_dummy_759 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_759 D R S_cls E),
                              (nb095_alpha_dummy_760 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_755 D R S_cls E),
                              (nb095_alpha_dummy_757 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_756 D R S_cls E),
                              (nb095_alpha_dummy_758 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_781 D R S_cls E),
                              (nb095_alpha_dummy_782 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_779 D R S_cls E),
                              (nb095_alpha_dummy_780 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_748 D R S_cls E),
                              (nb095_alpha_dummy_750 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_747 D R S_cls E),
                              (nb095_alpha_dummy_749 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_777 D R S_cls E),
                              (nb095_alpha_dummy_778 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_751 D R S_cls E),
                              (nb095_alpha_dummy_752 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_739 D R S_cls E),
                              (nb095_alpha_dummy_740 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_741 D R S_cls E),
                              (nb095_alpha_dummy_742 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_744 D R S_cls E),
                              (nb095_alpha_dummy_746 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_743 D R S_cls E),
                              (nb095_alpha_dummy_745 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_662 D R S_cls E),
                              (nb095_alpha_dummy_664 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_661 D R S_cls E),
                              (nb095_alpha_dummy_663 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_737 D R S_cls E),
                              (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                        (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
                              (nb095_alpha_dummy_759 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_759;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0798 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_760;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_755 D R S_cls E) ≠
                                (nb095_alpha_dummy_759 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_759 D R S_cls E),
                              (nb095_alpha_dummy_760 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_755 D R S_cls E),
                              (nb095_alpha_dummy_757 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_756 D R S_cls E),
                              (nb095_alpha_dummy_758 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_781 D R S_cls E),
                              (nb095_alpha_dummy_782 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_779 D R S_cls E),
                              (nb095_alpha_dummy_780 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_748 D R S_cls E),
                              (nb095_alpha_dummy_750 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_747 D R S_cls E),
                              (nb095_alpha_dummy_749 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_777 D R S_cls E),
                              (nb095_alpha_dummy_778 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_751 D R S_cls E),
                              (nb095_alpha_dummy_752 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_739 D R S_cls E),
                              (nb095_alpha_dummy_740 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_741 D R S_cls E),
                              (nb095_alpha_dummy_742 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_744 D R S_cls E),
                              (nb095_alpha_dummy_746 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_743 D R S_cls E),
                              (nb095_alpha_dummy_745 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_662 D R S_cls E),
                              (nb095_alpha_dummy_664 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_661 D R S_cls E),
                              (nb095_alpha_dummy_663 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_737 D R S_cls E),
                              (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                        (nb095_alpha_dummy_755 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_755;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                        (nb095_alpha_dummy_757 x u D R S_cls f E) from (by
                        unfold nb095_alpha_dummy_757;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0797 x u D R S_cls f E)
                                0)))) (TAlphaVar.there (show
                        (nb095_alpha_dummy_748 D R S_cls E) ≠
                          (nb095_alpha_dummy_756 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_756;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0796 D R S_cls E)
                                  1)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                          (nb095_alpha_dummy_758 x u D R S_cls f E) from (by
                          unfold nb095_alpha_dummy_758;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar
                                  (nb095_support_mem_0797 x u D R S_cls f E) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                            (nb095_alpha_dummy_781 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_781;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0826 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                            (nb095_alpha_dummy_782 x u D R S_cls f E) from (by
                            unfold nb095_alpha_dummy_782;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar
                                    (nb095_support_mem_0827 x u D R S_cls f E) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_748 D R S_cls E) ≠
                              (nb095_alpha_dummy_779 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_779;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0824 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_750 x u D R S_cls f E) ≠
                              (nb095_alpha_dummy_780 x u D R S_cls f E) from (by
                              unfold nb095_alpha_dummy_780;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb095_support_mem_0825 x u D R S_cls f E) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) (by decide))
                    (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_762 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_762;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0800 D R S_cls E)
                                                  1)))) (show
                                        (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_765 x u D R S_cls f E) from (by
                                          unfold nb095_alpha_dummy_765;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0801 x u D R S_cls f
                                                    E)
                                                  1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_755 D R S_cls E) ≠ (nb095_alpha_dummy_761 D R S_cls E) from (by
          unfold nb095_alpha_dummy_761;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0800 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_764 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_764;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0801 x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_755 D R S_cls E) ≠
        (nb095_alpha_dummy_759 D R S_cls E) from (by
          unfold nb095_alpha_dummy_759;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0798 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_760;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0799 x u D R
                    S_cls f E)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_763 D R S_cls E),
        (nb095_alpha_dummy_766 x u D R S_cls f E)), ((nb095_alpha_dummy_762 D R S_cls E),
        (nb095_alpha_dummy_765 x u D R S_cls f E)), ((nb095_alpha_dummy_761 D R S_cls E),
        (nb095_alpha_dummy_764 x u D R S_cls f E)), ((nb095_alpha_dummy_759 D R S_cls E),
        (nb095_alpha_dummy_760 x u D R S_cls f E)), ((nb095_alpha_dummy_755 D R S_cls E),
        (nb095_alpha_dummy_757 x u D R S_cls f E)), ((nb095_alpha_dummy_756 D R S_cls E),
        (nb095_alpha_dummy_758 x u D R S_cls f E)), ((nb095_alpha_dummy_781 D R S_cls E),
        (nb095_alpha_dummy_782 x u D R S_cls f E)), ((nb095_alpha_dummy_779 D R S_cls E),
        (nb095_alpha_dummy_780 x u D R S_cls f E)), ((nb095_alpha_dummy_748 D R S_cls E),
        (nb095_alpha_dummy_750 x u D R S_cls f E)), ((nb095_alpha_dummy_747 D R S_cls E),
        (nb095_alpha_dummy_749 x u D R S_cls f E)), ((nb095_alpha_dummy_777 D R S_cls E),
        (nb095_alpha_dummy_778 x u D R S_cls f E)), ((nb095_alpha_dummy_751 D R S_cls E),
        (nb095_alpha_dummy_752 x u D R S_cls f E)), ((nb095_alpha_dummy_739 D R S_cls E),
        (nb095_alpha_dummy_740 x u D R S_cls f E)), ((nb095_alpha_dummy_741 D R S_cls E),
        (nb095_alpha_dummy_742 x u D R S_cls f E)), ((nb095_alpha_dummy_744 D R S_cls E),
        (nb095_alpha_dummy_746 x u D R S_cls f E)), ((nb095_alpha_dummy_743 D R S_cls E),
        (nb095_alpha_dummy_745 x u D R S_cls f E)), ((nb095_alpha_dummy_662 D R S_cls E),
        (nb095_alpha_dummy_664 x u D R S_cls f E)), ((nb095_alpha_dummy_661 D R S_cls E),
        (nb095_alpha_dummy_663 x u D R S_cls f E)), ((nb095_alpha_dummy_737 D R S_cls E),
        (nb095_alpha_dummy_738 x u D R S_cls f E)), ((nb095_alpha_dummy_665 D R S_cls E),
        (nb095_alpha_dummy_666 x u D R S_cls f E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
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
        (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_769 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0804
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0805
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0802
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0803
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_769 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_769;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0808
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_770 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_770;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0809
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_767 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_767;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0806
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_768 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_768;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0807
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_763 D R S_cls E), (nb095_alpha_dummy_766 x u D R S_cls f E)),
        ((nb095_alpha_dummy_762 D R S_cls E), (nb095_alpha_dummy_765 x u D R S_cls f E)),
        ((nb095_alpha_dummy_761 D R S_cls E), (nb095_alpha_dummy_764 x u D R S_cls f E)),
        ((nb095_alpha_dummy_759 D R S_cls E), (nb095_alpha_dummy_760 x u D R S_cls f E)),
        ((nb095_alpha_dummy_755 D R S_cls E), (nb095_alpha_dummy_757 x u D R S_cls f E)),
        ((nb095_alpha_dummy_756 D R S_cls E), (nb095_alpha_dummy_758 x u D R S_cls f E)),
        ((nb095_alpha_dummy_781 D R S_cls E), (nb095_alpha_dummy_782 x u D R S_cls f E)),
        ((nb095_alpha_dummy_779 D R S_cls E), (nb095_alpha_dummy_780 x u D R S_cls f E)),
        ((nb095_alpha_dummy_748 D R S_cls E), (nb095_alpha_dummy_750 x u D R S_cls f E)),
        ((nb095_alpha_dummy_747 D R S_cls E), (nb095_alpha_dummy_749 x u D R S_cls f E)),
        ((nb095_alpha_dummy_777 D R S_cls E), (nb095_alpha_dummy_778 x u D R S_cls f E)),
        ((nb095_alpha_dummy_751 D R S_cls E), (nb095_alpha_dummy_752 x u D R S_cls f E)),
        ((nb095_alpha_dummy_739 D R S_cls E), (nb095_alpha_dummy_740 x u D R S_cls f E)),
        ((nb095_alpha_dummy_741 D R S_cls E), (nb095_alpha_dummy_742 x u D R S_cls f E)),
        ((nb095_alpha_dummy_744 D R S_cls E), (nb095_alpha_dummy_746 x u D R S_cls f E)),
        ((nb095_alpha_dummy_743 D R S_cls E), (nb095_alpha_dummy_745 x u D R S_cls f E)),
        ((nb095_alpha_dummy_662 D R S_cls E), (nb095_alpha_dummy_664 x u D R S_cls f E)),
        ((nb095_alpha_dummy_661 D R S_cls E), (nb095_alpha_dummy_663 x u D R S_cls f E)),
        ((nb095_alpha_dummy_737 D R S_cls E), (nb095_alpha_dummy_738 x u D R S_cls f E)),
        ((nb095_alpha_dummy_665 D R S_cls E), (nb095_alpha_dummy_666 x u D R S_cls f E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_762 D R S_cls E) ≠ (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_774 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_773 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_773;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0812
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_774 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_774;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0813
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_762 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0810
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_765 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0811
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_755
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_776 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_763 D R S_cls E) ≠ (nb095_alpha_dummy_775 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_775;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0816
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_776 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_776;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0817
                    x u D R S_cls f
                    E)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_763 D R S_cls E) ≠
        (nb095_alpha_dummy_771 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_771;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0814
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_766 x u D R S_cls f E) ≠
        (nb095_alpha_dummy_772 x u D R S_cls f E) from (by
          unfold
            nb095_alpha_dummy_772;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0815
                    x u D R S_cls
                    f E)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_755 D R S_cls E) ≠
                                  (nb095_alpha_dummy_759 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_759 D R S_cls E),
                                (nb095_alpha_dummy_760 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_755 D R S_cls E),
                                (nb095_alpha_dummy_757 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_756 D R S_cls E),
                                (nb095_alpha_dummy_758 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_781 D R S_cls E),
                                (nb095_alpha_dummy_782 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_779 D R S_cls E),
                                (nb095_alpha_dummy_780 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_748 D R S_cls E),
                                (nb095_alpha_dummy_750 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_747 D R S_cls E),
                                (nb095_alpha_dummy_749 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_777 D R S_cls E),
                                (nb095_alpha_dummy_778 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_751 D R S_cls E),
                                (nb095_alpha_dummy_752 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_739 D R S_cls E),
                                (nb095_alpha_dummy_740 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_741 D R S_cls E),
                                (nb095_alpha_dummy_742 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_744 D R S_cls E),
                                (nb095_alpha_dummy_746 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_743 D R S_cls E),
                                (nb095_alpha_dummy_745 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_662 D R S_cls E),
                                (nb095_alpha_dummy_664 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_661 D R S_cls E),
                                (nb095_alpha_dummy_663 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_737 D R S_cls E),
                                (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
                              (nb095_alpha_dummy_755 D R S_cls E) ≠
                                (nb095_alpha_dummy_759 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_759;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                unfold nb095_alpha_dummy_760;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_755 D R S_cls E) ≠
                                  (nb095_alpha_dummy_759 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_759;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0798 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_757 x u D R S_cls f E) ≠
                                  (nb095_alpha_dummy_760 x u D R S_cls f E) from (by
                                  unfold nb095_alpha_dummy_760;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0799 x u D R S_cls f E) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_759 D R S_cls E),
                                (nb095_alpha_dummy_760 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_755 D R S_cls E),
                                (nb095_alpha_dummy_757 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_756 D R S_cls E),
                                (nb095_alpha_dummy_758 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_781 D R S_cls E),
                                (nb095_alpha_dummy_782 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_779 D R S_cls E),
                                (nb095_alpha_dummy_780 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_748 D R S_cls E),
                                (nb095_alpha_dummy_750 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_747 D R S_cls E),
                                (nb095_alpha_dummy_749 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_777 D R S_cls E),
                                (nb095_alpha_dummy_778 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_751 D R S_cls E),
                                (nb095_alpha_dummy_752 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_739 D R S_cls E),
                                (nb095_alpha_dummy_740 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_741 D R S_cls E),
                                (nb095_alpha_dummy_742 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_744 D R S_cls E),
                                (nb095_alpha_dummy_746 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_743 D R S_cls E),
                                (nb095_alpha_dummy_745 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_662 D R S_cls E),
                                (nb095_alpha_dummy_664 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_661 D R S_cls E),
                                (nb095_alpha_dummy_663 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_737 D R S_cls E),
                                (nb095_alpha_dummy_738 x u D R S_cls f E)),
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
