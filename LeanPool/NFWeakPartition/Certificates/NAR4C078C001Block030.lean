/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block029

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part095`. -/


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
noncomputable def nb078_split_alpha_0068 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_697))
          (Class.cab (nb078_alpha_dummy_691)
            (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_697)) (Class.cab (nb078_alpha_dummy_691)
              (syn_wrex (nb078_alpha_dummy_692) (Class.cv (nb078_alpha_dummy_650))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_691))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_692)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_698 g))
          (Class.cab (nb078_alpha_dummy_693 g)
            (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_698 g))
            (Class.cab (nb078_alpha_dummy_693 g)
              (syn_wrex (nb078_alpha_dummy_694 g) (Class.cv (nb078_alpha_dummy_652 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_693 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_694 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_692) from
                    (by
                      unfold nb078_alpha_dummy_692;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
                  (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_694 g) from (by
                      unfold nb078_alpha_dummy_694;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_691) from
                      (by
                        unfold nb078_alpha_dummy_691;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
                    (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_693 g) from (by
                        unfold nb078_alpha_dummy_693;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0712 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_697) from (by
                          unfold nb078_alpha_dummy_697;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0714) 0))))
                      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_698 g) from (by
                          unfold nb078_alpha_dummy_698;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0715 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_695) from (by
                            unfold nb078_alpha_dummy_695;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0711) 0))))
                        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_696 g) from (by
                            unfold nb078_alpha_dummy_696;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0713 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_650))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_649))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_651 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_699) from (by
                              unfold nb078_alpha_dummy_699;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                          (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_701 g) from (by
                              unfold nb078_alpha_dummy_701;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_700) from (by
                                unfold nb078_alpha_dummy_700;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                            (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_702 g) from (by
                                unfold nb078_alpha_dummy_702;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_694 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_706) from (by
          unfold nb078_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 1)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_709 g) from (by
          unfold nb078_alpha_dummy_709;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_705) from (by
          unfold nb078_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_708 g) from (by
          unfold nb078_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
          unfold nb078_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_704 g) from (by
          unfold nb078_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706),
        (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699),
        (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691),
        (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706),
        (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699),
        (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691),
        (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_717) from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_717)
        from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠
        (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                        unfold nb078_alpha_dummy_703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078_alpha_dummy_701 g) ≠
                                        (nb078_alpha_dummy_704 g) from (by
                                        unfold nb078_alpha_dummy_704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                                    ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                                    ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                                    ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                                    ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                                    ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
                                    ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from
                                    (by
                                      unfold nb078_alpha_dummy_703;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0718)
                                              0)))) (show
                                    (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from
                                    (by
                                      unfold nb078_alpha_dummy_704;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0719 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                        unfold nb078_alpha_dummy_703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078_alpha_dummy_701 g) ≠
                                        (nb078_alpha_dummy_704 g) from (by
                                        unfold nb078_alpha_dummy_704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                                    ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                                    ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                                    ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                                    ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                                    ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
                                    ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_692) from
                      (by
                        unfold nb078_alpha_dummy_692;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
                    (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_694 g) from (by
                        unfold nb078_alpha_dummy_694;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0712 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_691) from (by
                          unfold nb078_alpha_dummy_691;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0710) 0))))
                      (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_693 g) from (by
                          unfold nb078_alpha_dummy_693;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_697) from (by
                            unfold nb078_alpha_dummy_697;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0714) 0))))
                        (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_698 g) from (by
                            unfold nb078_alpha_dummy_698;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0715 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_695) from (by
                              unfold nb078_alpha_dummy_695;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0711) 0))))
                          (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_696 g) from (by
                              unfold nb078_alpha_dummy_696;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0713 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_650))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_649))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_651 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_699) from (by
                                unfold nb078_alpha_dummy_699;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                            (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_701 g) from (by
                                unfold nb078_alpha_dummy_701;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_700) from (by
                                  unfold nb078_alpha_dummy_700;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                              (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_702 g) from
                                (by
                                  unfold nb078_alpha_dummy_702;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_694 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_706) from (by
          unfold nb078_alpha_dummy_706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 1)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_709 g) from (by
          unfold nb078_alpha_dummy_709;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_705) from (by
          unfold nb078_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_708 g) from (by
          unfold nb078_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703)
        from (by
          unfold nb078_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718)
                  0)))) (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from (by
          unfold nb078_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706),
        (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699),
        (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691),
        (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706),
        (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699),
        (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691),
        (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_699))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_701
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_717) from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_717)
        from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠
        (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from
                                        (by
                                          unfold nb078_alpha_dummy_703;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0718)
                                                  0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_704 g) from (by
                                          unfold nb078_alpha_dummy_704;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0719 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                                      ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                                      ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                                      ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                                      ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                                      ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
                                      ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                        unfold nb078_alpha_dummy_703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078_alpha_dummy_701 g) ≠
                                        (nb078_alpha_dummy_704 g) from (by
                                        unfold nb078_alpha_dummy_704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from
                                        (by
                                          unfold nb078_alpha_dummy_703;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0718)
                                                  0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_704 g) from (by
                                          unfold nb078_alpha_dummy_704;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0719 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                                      ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                                      ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                                      ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                                      ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                                      ((nb078_alpha_dummy_697), (nb078_alpha_dummy_698 g)),
                                      ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part096`. -/


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
noncomputable def nb078_split_alpha_0069 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
        ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
        ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
        ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_725))
          (syn_cphi (Class.cv (nb078_alpha_dummy_692)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_725))
            (syn_cphi (Class.cv (nb078_alpha_dummy_692))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_726 g))
          (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_726 g))
            (syn_cphi (Class.cv (nb078_alpha_dummy_694 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_699) from
                    (by
                      unfold nb078_alpha_dummy_699;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                  (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_701 g) from (by
                      unfold nb078_alpha_dummy_701;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_700) from
                      (by
                        unfold nb078_alpha_dummy_700;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                    (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_702 g) from (by
                        unfold nb078_alpha_dummy_702;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0717 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_725) from (by
                          unfold nb078_alpha_dummy_725;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0746) 0))))
                      (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_726 g) from (by
                          unfold nb078_alpha_dummy_726;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0747 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_723) from (by
                            unfold nb078_alpha_dummy_723;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0744) 0))))
                        (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_724 g) from (by
                            unfold nb078_alpha_dummy_724;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0745 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_694 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_706) from (by
                                        unfold nb078_alpha_dummy_706;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0720)
                                                1)))) (show (nb078_alpha_dummy_701 g) ≠
                                        (nb078_alpha_dummy_709 g) from (by
                                        unfold nb078_alpha_dummy_709;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0721 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_705) from
                                        (by
                                          unfold nb078_alpha_dummy_705;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0720)
                                                  0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_708 g) from (by
                                          unfold nb078_alpha_dummy_708;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0721 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_699) ≠
        (nb078_alpha_dummy_703) from (by
          unfold nb078_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_704 g) from (by
          unfold nb078_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_707),
        (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706), (nb078_alpha_dummy_709 g)),
                                        ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
                                        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                                        ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                                        ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                                        ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
                                        ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
                                        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                                        ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                                        ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
                                        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                                        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                        ((nb078_alpha_dummy_001), g),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)),
        ((nb078_alpha_dummy_706), (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705),
        (nb078_alpha_dummy_708 g)), ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
        ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700),
        (nb078_alpha_dummy_702 g)), ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
        ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)), ((nb078_alpha_dummy_692),
        (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
        ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)), ((nb078_alpha_dummy_695),
        (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_717) from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_717)
        from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠
        (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                unfold nb078_alpha_dummy_703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from (by
                                unfold nb078_alpha_dummy_704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                            ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                            ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                            ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
                            ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
                            ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                            ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                            ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
                            ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                            ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                            ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                            ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                              unfold nb078_alpha_dummy_703;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                          (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from (by
                              unfold nb078_alpha_dummy_704;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                unfold nb078_alpha_dummy_703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from (by
                                unfold nb078_alpha_dummy_704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                            ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                            ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                            ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
                            ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
                            ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                            ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                            ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
                            ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                            ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                            ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                            ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                            ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                            ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                            ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                            ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_699) from (by
                        unfold nb078_alpha_dummy_699;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                    (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_701 g) from (by
                        unfold nb078_alpha_dummy_701;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0717 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_700) from (by
                          unfold nb078_alpha_dummy_700;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                      (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_702 g) from (by
                          unfold nb078_alpha_dummy_702;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_725) from (by
                            unfold nb078_alpha_dummy_725;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0746) 0))))
                        (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_726 g) from (by
                            unfold nb078_alpha_dummy_726;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0747 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_692) ≠ (nb078_alpha_dummy_723) from (by
                              unfold nb078_alpha_dummy_723;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0744) 0))))
                          (show (nb078_alpha_dummy_694 g) ≠ (nb078_alpha_dummy_724 g) from (by
                              unfold nb078_alpha_dummy_724;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0745 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_692))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_694 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_706) from
                                        (by
                                          unfold nb078_alpha_dummy_706;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0720)
                                                  1)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_709 g) from (by
                                          unfold nb078_alpha_dummy_709;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0721 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_699) ≠
        (nb078_alpha_dummy_705) from (by
          unfold nb078_alpha_dummy_705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_708 g) from (by
          unfold nb078_alpha_dummy_708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
          unfold nb078_alpha_dummy_703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078_alpha_dummy_701 g) ≠
        (nb078_alpha_dummy_704 g) from (by
          unfold nb078_alpha_dummy_704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_707),
        (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706), (nb078_alpha_dummy_709 g)),
        ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)), ((nb078_alpha_dummy_703),
        (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
        ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)), ((nb078_alpha_dummy_725),
        (nb078_alpha_dummy_726 g)), ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
        ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691),
        (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
        ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_713) from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_713)
        from (by
          unfold
            nb078_alpha_dummy_713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_714 g) from (by
          unfold
            nb078_alpha_dummy_714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_711)
        from (by
          unfold
            nb078_alpha_dummy_711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_712 g) from (by
          unfold
            nb078_alpha_dummy_712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_707), (nb078_alpha_dummy_710 g)), ((nb078_alpha_dummy_706),
        (nb078_alpha_dummy_709 g)), ((nb078_alpha_dummy_705), (nb078_alpha_dummy_708 g)),
        ((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)), ((nb078_alpha_dummy_699),
        (nb078_alpha_dummy_701 g)), ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
        ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)), ((nb078_alpha_dummy_723),
        (nb078_alpha_dummy_724 g)), ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
        ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)), ((nb078_alpha_dummy_721),
        (nb078_alpha_dummy_722 g)), ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649),
        (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠
        (nb078_alpha_dummy_717) from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_717)
        from (by
          unfold
            nb078_alpha_dummy_717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_718 g) from (by
          unfold
            nb078_alpha_dummy_718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_706) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078_alpha_dummy_709 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_699))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_701 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠
        (nb078_alpha_dummy_719) from (by
          unfold
            nb078_alpha_dummy_719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_720 g) from (by
          unfold
            nb078_alpha_dummy_720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_707) ≠ (nb078_alpha_dummy_715)
        from (by
          unfold
            nb078_alpha_dummy_715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078_alpha_dummy_710 g) ≠ (nb078_alpha_dummy_716 g) from (by
          unfold
            nb078_alpha_dummy_716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                  unfold nb078_alpha_dummy_703;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                              (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from
                                (by
                                  unfold nb078_alpha_dummy_704;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                              ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                              ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                              ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
                              ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
                              ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                              ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                              ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
                              ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                              ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                              ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                              ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                unfold nb078_alpha_dummy_703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from (by
                                unfold nb078_alpha_dummy_704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_699) ≠ (nb078_alpha_dummy_703) from (by
                                  unfold nb078_alpha_dummy_703;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                              (show (nb078_alpha_dummy_701 g) ≠ (nb078_alpha_dummy_704 g) from
                                (by
                                  unfold nb078_alpha_dummy_704;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_703), (nb078_alpha_dummy_704 g)),
                              ((nb078_alpha_dummy_699), (nb078_alpha_dummy_701 g)),
                              ((nb078_alpha_dummy_700), (nb078_alpha_dummy_702 g)),
                              ((nb078_alpha_dummy_725), (nb078_alpha_dummy_726 g)),
                              ((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)),
                              ((nb078_alpha_dummy_692), (nb078_alpha_dummy_694 g)),
                              ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
                              ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)),
                              ((nb078_alpha_dummy_695), (nb078_alpha_dummy_696 g)),
                              ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                              ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                              ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part097`. -/


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
noncomputable def nb078_split_alpha_0070 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_379))
          (Class.cab (nb078_alpha_dummy_373)
            (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                (syn_cphi (Class.cv (nb078_alpha_dummy_374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_379)) (Class.cab (nb078_alpha_dummy_373)
              (syn_wrex (nb078_alpha_dummy_374) (Class.cv (nb078_alpha_dummy_367))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_373))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
          (Class.cab (nb078_alpha_dummy_375 g)
            (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_380 g))
            (Class.cab (nb078_alpha_dummy_375 g)
              (syn_wrex (nb078_alpha_dummy_376 g) (Class.cv (nb078_alpha_dummy_369 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_375 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                    (by
                      unfold nb078_alpha_dummy_374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                      unfold nb078_alpha_dummy_376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from
                      (by
                        unfold nb078_alpha_dummy_373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                        unfold nb078_alpha_dummy_375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                          unfold nb078_alpha_dummy_379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                          unfold nb078_alpha_dummy_380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                            unfold nb078_alpha_dummy_377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                            unfold nb078_alpha_dummy_378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                              unfold nb078_alpha_dummy_381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                              unfold nb078_alpha_dummy_383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                unfold nb078_alpha_dummy_382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from (by
                                unfold nb078_alpha_dummy_384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                    (by
                                      unfold nb078_alpha_dummy_385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from
                                    (by
                                      unfold nb078_alpha_dummy_386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                    ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                    ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                    ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                    ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                    ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                    ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                    ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                    ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_374) from
                      (by
                        unfold nb078_alpha_dummy_374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_376 g) from (by
                        unfold nb078_alpha_dummy_376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_373) from (by
                          unfold nb078_alpha_dummy_373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_375 g) from (by
                          unfold nb078_alpha_dummy_375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_379) from (by
                            unfold nb078_alpha_dummy_379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_380 g) from (by
                            unfold nb078_alpha_dummy_380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_377) from (by
                              unfold nb078_alpha_dummy_377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_378 g) from (by
                              unfold nb078_alpha_dummy_378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_367))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_369 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_381) from (by
                                unfold nb078_alpha_dummy_381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_383 g) from (by
                                unfold nb078_alpha_dummy_383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_374) ≠ (nb078_alpha_dummy_382) from (by
                                  unfold nb078_alpha_dummy_382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078_alpha_dummy_376 g) ≠ (nb078_alpha_dummy_384 g) from
                                (by
                                  unfold nb078_alpha_dummy_384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_388) from (by
          unfold nb078_alpha_dummy_388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_391 g) from (by
          unfold nb078_alpha_dummy_391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_387) from (by
          unfold nb078_alpha_dummy_387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_390 g) from (by
          unfold nb078_alpha_dummy_390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385)
        from (by
          unfold nb078_alpha_dummy_385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078_alpha_dummy_383 g) ≠ (nb078_alpha_dummy_386 g) from (by
          unfold nb078_alpha_dummy_386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_395) from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_395)
        from (by
          unfold
            nb078_alpha_dummy_395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_396 g) from (by
          unfold
            nb078_alpha_dummy_396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_393)
        from (by
          unfold
            nb078_alpha_dummy_393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_394 g) from (by
          unfold
            nb078_alpha_dummy_394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_389), (nb078_alpha_dummy_392 g)), ((nb078_alpha_dummy_388),
        (nb078_alpha_dummy_391 g)), ((nb078_alpha_dummy_387), (nb078_alpha_dummy_390 g)),
        ((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)), ((nb078_alpha_dummy_381),
        (nb078_alpha_dummy_383 g)), ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
        ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373),
        (nb078_alpha_dummy_375 g)), ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
        ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_381))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_383
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠
        (nb078_alpha_dummy_399) from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_399)
        from (by
          unfold
            nb078_alpha_dummy_399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_400 g) from (by
          unfold
            nb078_alpha_dummy_400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_388) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078_alpha_dummy_391 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_381))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_383 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠
        (nb078_alpha_dummy_401) from (by
          unfold
            nb078_alpha_dummy_401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_402 g) from (by
          unfold
            nb078_alpha_dummy_402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_389) ≠ (nb078_alpha_dummy_397)
        from (by
          unfold
            nb078_alpha_dummy_397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078_alpha_dummy_392 g) ≠ (nb078_alpha_dummy_398 g) from (by
          unfold
            nb078_alpha_dummy_398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from (by
                                        unfold nb078_alpha_dummy_385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078_alpha_dummy_383 g) ≠
                                        (nb078_alpha_dummy_386 g) from (by
                                        unfold nb078_alpha_dummy_386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_381) ≠ (nb078_alpha_dummy_385) from
                                        (by
                                          unfold nb078_alpha_dummy_385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078_alpha_dummy_383 g) ≠
        (nb078_alpha_dummy_386 g) from (by
                                          unfold nb078_alpha_dummy_386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_385), (nb078_alpha_dummy_386 g)),
                                      ((nb078_alpha_dummy_381), (nb078_alpha_dummy_383 g)),
                                      ((nb078_alpha_dummy_382), (nb078_alpha_dummy_384 g)),
                                      ((nb078_alpha_dummy_374), (nb078_alpha_dummy_376 g)),
                                      ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
                                      ((nb078_alpha_dummy_379), (nb078_alpha_dummy_380 g)),
                                      ((nb078_alpha_dummy_377), (nb078_alpha_dummy_378 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                      ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
                                      ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
                                      ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
