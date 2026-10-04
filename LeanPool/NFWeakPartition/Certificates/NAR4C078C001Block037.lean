/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block036

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part113`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0088`. -/
@[expose]
noncomputable def nb078SplitAlpha0088 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy697))
          (Class.cab (nb078AlphaDummy691)
            (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
              (Wff.classEq (Class.cv (nb078AlphaDummy691))
                (synCphi (Class.cv (nb078AlphaDummy692))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy697)) (Class.cab (nb078AlphaDummy691)
              (synWrex (nb078AlphaDummy692) (Class.cv (nb078AlphaDummy650))
                (Wff.classEq (Class.cv (nb078AlphaDummy691))
                  (synCphi (Class.cv (nb078AlphaDummy692)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy698 g))
          (Class.cab (nb078AlphaDummy693 g)
            (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                (synCphi (Class.cv (nb078AlphaDummy694 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy698 g))
            (Class.cab (nb078AlphaDummy693 g)
              (synWrex (nb078AlphaDummy694 g) (Class.cv (nb078AlphaDummy652 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy693 g))
                  (synCphi (Class.cv (nb078AlphaDummy694 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy692) from
                    (by
                      unfold nb078AlphaDummy692;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
                  (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy694 g) from (by
                      unfold nb078AlphaDummy694;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0712 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy691) from
                      (by
                        unfold nb078AlphaDummy691;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 0))))
                    (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy693 g) from (by
                        unfold nb078AlphaDummy693;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0712 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy697) from (by
                          unfold nb078AlphaDummy697;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0714) 0))))
                      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy698 g) from (by
                          unfold nb078AlphaDummy698;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0715 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy695) from (by
                            unfold nb078AlphaDummy695;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0711) 0))))
                        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy696 g) from (by
                            unfold nb078AlphaDummy696;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0713 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy650))).fv ∪
                      ((Class.cv (nb078AlphaDummy649))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy652 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy651 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy699) from (by
                              unfold nb078AlphaDummy699;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                          (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy701 g) from (by
                              unfold nb078AlphaDummy701;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy700) from (by
                                unfold nb078AlphaDummy700;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                            (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy702 g) from (by
                                unfold nb078AlphaDummy702;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy692))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy694 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy706) from (by
          unfold nb078AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 1)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy709 g) from (by
          unfold nb078AlphaDummy709;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy699) ≠ (nb078AlphaDummy705) from (by
          unfold nb078AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy708 g) from (by
          unfold nb078AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
          unfold nb078AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy704 g) from (by
          unfold nb078AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)), ((nb078AlphaDummy706),
        (nb078AlphaDummy709 g)), ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)), ((nb078AlphaDummy699),
        (nb078AlphaDummy701 g)), ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)), ((nb078AlphaDummy691),
        (nb078AlphaDummy693 g)), ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)), ((nb078AlphaDummy706),
        (nb078AlphaDummy709 g)), ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)), ((nb078AlphaDummy699),
        (nb078AlphaDummy701 g)), ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)), ((nb078AlphaDummy691),
        (nb078AlphaDummy693 g)), ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy701
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717) from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717)
        from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠
        (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                        unfold nb078AlphaDummy703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078AlphaDummy701 g) ≠
                                        (nb078AlphaDummy704 g) from (by
                                        unfold nb078AlphaDummy704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                                    ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                                    ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                                    ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                                    ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                                    ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
                                    ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from
                                    (by
                                      unfold nb078AlphaDummy703;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0718)
                                              0)))) (show
                                    (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from
                                    (by
                                      unfold nb078AlphaDummy704;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0719 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                        unfold nb078AlphaDummy703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078AlphaDummy701 g) ≠
                                        (nb078AlphaDummy704 g) from (by
                                        unfold nb078AlphaDummy704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                                    ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                                    ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                                    ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                                    ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                                    ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
                                    ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy692) from
                      (by
                        unfold nb078AlphaDummy692;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0710) 1))))
                    (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy694 g) from (by
                        unfold nb078AlphaDummy694;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0712 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy691) from (by
                          unfold nb078AlphaDummy691;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0710) 0))))
                      (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy693 g) from (by
                          unfold nb078AlphaDummy693;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0712 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy697) from (by
                            unfold nb078AlphaDummy697;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0714) 0))))
                        (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy698 g) from (by
                            unfold nb078AlphaDummy698;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0715 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy650) ≠ (nb078AlphaDummy695) from (by
                              unfold nb078AlphaDummy695;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0711) 0))))
                          (show (nb078AlphaDummy652 g) ≠ (nb078AlphaDummy696 g) from (by
                              unfold nb078AlphaDummy696;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0713 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy650))).fv ∪
                        ((Class.cv (nb078AlphaDummy649))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy652 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy651 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy699) from (by
                                unfold nb078AlphaDummy699;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                            (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy701 g) from (by
                                unfold nb078AlphaDummy701;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy700) from (by
                                  unfold nb078AlphaDummy700;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                              (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy702 g) from
                                (by
                                  unfold nb078AlphaDummy702;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy692))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy694 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy699) ≠ (nb078AlphaDummy706) from (by
          unfold nb078AlphaDummy706;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 1)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy709 g) from (by
          unfold nb078AlphaDummy709;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy699) ≠ (nb078AlphaDummy705) from (by
          unfold nb078AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy708 g) from (by
          unfold nb078AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703)
        from (by
          unfold nb078AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718)
                  0)))) (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from (by
          unfold nb078AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)), ((nb078AlphaDummy706),
        (nb078AlphaDummy709 g)), ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)), ((nb078AlphaDummy699),
        (nb078AlphaDummy701 g)), ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)), ((nb078AlphaDummy691),
        (nb078AlphaDummy693 g)), ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)), ((nb078AlphaDummy706),
        (nb078AlphaDummy709 g)), ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)), ((nb078AlphaDummy699),
        (nb078AlphaDummy701 g)), ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)), ((nb078AlphaDummy691),
        (nb078AlphaDummy693 g)), ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy701
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717) from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717)
        from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠
        (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from
                                        (by
                                          unfold nb078AlphaDummy703;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0718)
                                                  0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy704 g) from (by
                                          unfold nb078AlphaDummy704;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0719 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                                      ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                                      ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                                      ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                                      ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                                      ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
                                      ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                        unfold nb078AlphaDummy703;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0718)
                                                0)))) (show (nb078AlphaDummy701 g) ≠
                                        (nb078AlphaDummy704 g) from (by
                                        unfold nb078AlphaDummy704;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0719 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from
                                        (by
                                          unfold nb078AlphaDummy703;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0718)
                                                  0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy704 g) from (by
                                          unfold nb078AlphaDummy704;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0719 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                                      ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                                      ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                                      ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                                      ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                                      ((nb078AlphaDummy697), (nb078AlphaDummy698 g)),
                                      ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part114`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0089`. -/
@[expose]
noncomputable def nb078SplitAlpha0089 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
        ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
        ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
        ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy725))
          (synCphi (Class.cv (nb078AlphaDummy692)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy725))
            (synCphi (Class.cv (nb078AlphaDummy692))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy726 g))
          (synCphi (Class.cv (nb078AlphaDummy694 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy726 g))
            (synCphi (Class.cv (nb078AlphaDummy694 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy699) from
                    (by
                      unfold nb078AlphaDummy699;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                  (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy701 g) from (by
                      unfold nb078AlphaDummy701;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0717 g) 0))))
                  (TAlphaVar.there (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy700) from
                      (by
                        unfold nb078AlphaDummy700;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                    (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy702 g) from (by
                        unfold nb078AlphaDummy702;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0717 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy725) from (by
                          unfold nb078AlphaDummy725;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0746) 0))))
                      (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy726 g) from (by
                          unfold nb078AlphaDummy726;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0747 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy723) from (by
                            unfold nb078AlphaDummy723;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0744) 0))))
                        (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy724 g) from (by
                            unfold nb078AlphaDummy724;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0745 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy692))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy694 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy699) ≠ (nb078AlphaDummy706) from (by
                                        unfold nb078AlphaDummy706;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0720)
                                                1)))) (show (nb078AlphaDummy701 g) ≠
                                        (nb078AlphaDummy709 g) from (by
                                        unfold nb078AlphaDummy709;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0721 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy699) ≠ (nb078AlphaDummy705) from
                                        (by
                                          unfold nb078AlphaDummy705;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0720)
                                                  0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy708 g) from (by
                                          unfold nb078AlphaDummy708;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0721 g) 0))))
                                      (TAlphaVar.there (show (nb078AlphaDummy699) ≠
        (nb078AlphaDummy703) from (by
          unfold nb078AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy704 g) from (by
          unfold nb078AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb078AlphaDummy707),
        (nb078AlphaDummy710 g)), ((nb078AlphaDummy706), (nb078AlphaDummy709 g)),
                                        ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
                                        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                                        ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                                        ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                                        ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
                                        ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
                                        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                                        ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                                        ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
                                        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                                        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                        ((nb078AlphaDummy001), g),
                                        ((nb078AlphaDummy004), y),
                                        ((nb078AlphaDummy003), x)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠
        (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)),
        ((nb078AlphaDummy706), (nb078AlphaDummy709 g)), ((nb078AlphaDummy705),
        (nb078AlphaDummy708 g)), ((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
        ((nb078AlphaDummy699), (nb078AlphaDummy701 g)), ((nb078AlphaDummy700),
        (nb078AlphaDummy702 g)), ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
        ((nb078AlphaDummy723), (nb078AlphaDummy724 g)), ((nb078AlphaDummy692),
        (nb078AlphaDummy694 g)), ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
        ((nb078AlphaDummy721), (nb078AlphaDummy722 g)), ((nb078AlphaDummy695),
        (nb078AlphaDummy696 g)), ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)), ((nb078AlphaDummy653),
        (nb078AlphaDummy654 g)), ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠
        (nb078AlphaDummy717) from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717)
        from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠
        (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                unfold nb078AlphaDummy703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from (by
                                unfold nb078AlphaDummy704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                            ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                            ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                            ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
                            ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
                            ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                            ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                            ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
                            ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                              unfold nb078AlphaDummy703;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                          (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from (by
                              unfold nb078AlphaDummy704;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                unfold nb078AlphaDummy703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from (by
                                unfold nb078AlphaDummy704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                            ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                            ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                            ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
                            ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
                            ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                            ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                            ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
                            ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                            ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                            ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                            ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                            ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                            ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                            ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                            ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                            ((nb078AlphaDummy003), x)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy699) from (by
                        unfold nb078AlphaDummy699;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0716) 0))))
                    (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy701 g) from (by
                        unfold nb078AlphaDummy701;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0717 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy700) from (by
                          unfold nb078AlphaDummy700;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0716) 1))))
                      (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy702 g) from (by
                          unfold nb078AlphaDummy702;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0717 g) 1))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy725) from (by
                            unfold nb078AlphaDummy725;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0746) 0))))
                        (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy726 g) from (by
                            unfold nb078AlphaDummy726;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0747 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy692) ≠ (nb078AlphaDummy723) from (by
                              unfold nb078AlphaDummy723;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0744) 0))))
                          (show (nb078AlphaDummy694 g) ≠ (nb078AlphaDummy724 g) from (by
                              unfold nb078AlphaDummy724;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0745 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy692))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy694 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078AlphaDummy699) ≠ (nb078AlphaDummy706) from
                                        (by
                                          unfold nb078AlphaDummy706;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0720)
                                                  1)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy709 g) from (by
                                          unfold nb078AlphaDummy709;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0721 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy699) ≠
        (nb078AlphaDummy705) from (by
          unfold nb078AlphaDummy705;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0720) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy708 g) from (by
          unfold nb078AlphaDummy708;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0721 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
          unfold nb078AlphaDummy703;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0718) 0)))) (show (nb078AlphaDummy701 g) ≠
        (nb078AlphaDummy704 g) from (by
          unfold nb078AlphaDummy704;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0719 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb078AlphaDummy707),
        (nb078AlphaDummy710 g)), ((nb078AlphaDummy706), (nb078AlphaDummy709 g)),
        ((nb078AlphaDummy705), (nb078AlphaDummy708 g)), ((nb078AlphaDummy703),
        (nb078AlphaDummy704 g)), ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
        ((nb078AlphaDummy700), (nb078AlphaDummy702 g)), ((nb078AlphaDummy725),
        (nb078AlphaDummy726 g)), ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
        ((nb078AlphaDummy692), (nb078AlphaDummy694 g)), ((nb078AlphaDummy691),
        (nb078AlphaDummy693 g)), ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
        ((nb078AlphaDummy695), (nb078AlphaDummy696 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠
        (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy713) from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0724)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0725
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0722)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0723
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy713)
        from (by
          unfold
            nb078AlphaDummy713;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0728)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy714 g) from (by
          unfold
            nb078AlphaDummy714;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0729
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy711)
        from (by
          unfold
            nb078AlphaDummy711;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0726)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy712 g) from (by
          unfold
            nb078AlphaDummy712;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0727
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy707), (nb078AlphaDummy710 g)), ((nb078AlphaDummy706),
        (nb078AlphaDummy709 g)), ((nb078AlphaDummy705), (nb078AlphaDummy708 g)),
        ((nb078AlphaDummy703), (nb078AlphaDummy704 g)), ((nb078AlphaDummy699),
        (nb078AlphaDummy701 g)), ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
        ((nb078AlphaDummy725), (nb078AlphaDummy726 g)), ((nb078AlphaDummy723),
        (nb078AlphaDummy724 g)), ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
        ((nb078AlphaDummy691), (nb078AlphaDummy693 g)), ((nb078AlphaDummy721),
        (nb078AlphaDummy722 g)), ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)), ((nb078AlphaDummy649),
        (nb078AlphaDummy651 g)), ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy699))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠
        (nb078AlphaDummy717) from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy717)
        from (by
          unfold
            nb078AlphaDummy717;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0732)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy718 g) from (by
          unfold
            nb078AlphaDummy718;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0733
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy706) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0730)
                  0)))) (show (nb078AlphaDummy709 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0731
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy699))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy701 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy707) ≠
        (nb078AlphaDummy719) from (by
          unfold
            nb078AlphaDummy719;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0736)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy720 g) from (by
          unfold
            nb078AlphaDummy720;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0737
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy707) ≠ (nb078AlphaDummy715)
        from (by
          unfold
            nb078AlphaDummy715;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0734)
                  0)))) (show (nb078AlphaDummy710 g) ≠ (nb078AlphaDummy716 g) from (by
          unfold
            nb078AlphaDummy716;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0735
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                  unfold nb078AlphaDummy703;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                              (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from
                                (by
                                  unfold nb078AlphaDummy704;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                              ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                              ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                              ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
                              ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
                              ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                              ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                              ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
                              ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                unfold nb078AlphaDummy703;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                            (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from (by
                                unfold nb078AlphaDummy704;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078AlphaDummy699) ≠ (nb078AlphaDummy703) from (by
                                  unfold nb078AlphaDummy703;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0718) 0))))
                              (show (nb078AlphaDummy701 g) ≠ (nb078AlphaDummy704 g) from
                                (by
                                  unfold nb078AlphaDummy704;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0719 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb078AlphaDummy703), (nb078AlphaDummy704 g)),
                              ((nb078AlphaDummy699), (nb078AlphaDummy701 g)),
                              ((nb078AlphaDummy700), (nb078AlphaDummy702 g)),
                              ((nb078AlphaDummy725), (nb078AlphaDummy726 g)),
                              ((nb078AlphaDummy723), (nb078AlphaDummy724 g)),
                              ((nb078AlphaDummy692), (nb078AlphaDummy694 g)),
                              ((nb078AlphaDummy691), (nb078AlphaDummy693 g)),
                              ((nb078AlphaDummy721), (nb078AlphaDummy722 g)),
                              ((nb078AlphaDummy695), (nb078AlphaDummy696 g)),
                              ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                              ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                              ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                              ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                              ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                              ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                              ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                              ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                              ((nb078AlphaDummy003), x)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part115`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0090`. -/
@[expose]
noncomputable def nb078SplitAlpha0090 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
        ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
        ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
        ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
        ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy379))
          (Class.cab (nb078AlphaDummy373)
            (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
              (Wff.classEq (Class.cv (nb078AlphaDummy373))
                (synCphi (Class.cv (nb078AlphaDummy374))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy379)) (Class.cab (nb078AlphaDummy373)
              (synWrex (nb078AlphaDummy374) (Class.cv (nb078AlphaDummy367))
                (Wff.classEq (Class.cv (nb078AlphaDummy373))
                  (synCphi (Class.cv (nb078AlphaDummy374)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
          (Class.cab (nb078AlphaDummy375 g)
            (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                (synCphi (Class.cv (nb078AlphaDummy376 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy380 g))
            (Class.cab (nb078AlphaDummy375 g)
              (synWrex (nb078AlphaDummy376 g) (Class.cv (nb078AlphaDummy369 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy375 g))
                  (synCphi (Class.cv (nb078AlphaDummy376 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                    (by
                      unfold nb078AlphaDummy374;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                  (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                      unfold nb078AlphaDummy376;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0376 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from
                      (by
                        unfold nb078AlphaDummy373;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                        unfold nb078AlphaDummy375;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                          unfold nb078AlphaDummy379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                          unfold nb078AlphaDummy380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                            unfold nb078AlphaDummy377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                            unfold nb078AlphaDummy378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy367))).fv ∪
                      ((Class.cv (nb078AlphaDummy368))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                              unfold nb078AlphaDummy381;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                          (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                              unfold nb078AlphaDummy383;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                unfold nb078AlphaDummy382;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from (by
                                unfold nb078AlphaDummy384;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy376 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                    (by
                                      unfold nb078AlphaDummy385;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0382)
                                              0)))) (show
                                    (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from
                                    (by
                                      unfold nb078AlphaDummy386;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0383 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                    ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                    ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                    ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                    ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                    ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                    ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                    ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                    ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                    ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                    ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                    ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                    ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy374) from
                      (by
                        unfold nb078AlphaDummy374;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0374) 1))))
                    (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy376 g) from (by
                        unfold nb078AlphaDummy376;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0376 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy373) from (by
                          unfold nb078AlphaDummy373;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0374) 0))))
                      (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy375 g) from (by
                          unfold nb078AlphaDummy375;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0376 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy379) from (by
                            unfold nb078AlphaDummy379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0378) 0))))
                        (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy380 g) from (by
                            unfold nb078AlphaDummy380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0379 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy367) ≠ (nb078AlphaDummy377) from (by
                              unfold nb078AlphaDummy377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0375) 0))))
                          (show (nb078AlphaDummy369 g) ≠ (nb078AlphaDummy378 g) from (by
                              unfold nb078AlphaDummy378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0377 g) 0))))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv g)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy367))).fv ∪
                        ((Class.cv (nb078AlphaDummy368))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy369 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy370 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy381) from (by
                                unfold nb078AlphaDummy381;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0380) 0))))
                            (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy383 g) from (by
                                unfold nb078AlphaDummy383;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0381 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy374) ≠ (nb078AlphaDummy382) from (by
                                  unfold nb078AlphaDummy382;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0380) 1))))
                              (show (nb078AlphaDummy376 g) ≠ (nb078AlphaDummy384 g) from
                                (by
                                  unfold nb078AlphaDummy384;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0381 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy374))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy376 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy388) from (by
          unfold nb078AlphaDummy388;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 1)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy391 g) from (by
          unfold nb078AlphaDummy391;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy381) ≠ (nb078AlphaDummy387) from (by
          unfold nb078AlphaDummy387;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0384) 0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy390 g) from (by
          unfold nb078AlphaDummy390;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0385 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy381) ≠ (nb078AlphaDummy385)
        from (by
          unfold nb078AlphaDummy385;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0382)
                  0)))) (show (nb078AlphaDummy383 g) ≠ (nb078AlphaDummy386 g) from (by
          unfold nb078AlphaDummy386;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0383 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy395) from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0388)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0389
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0386)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0387
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy395)
        from (by
          unfold
            nb078AlphaDummy395;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0392)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy396 g) from (by
          unfold
            nb078AlphaDummy396;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0393
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy393)
        from (by
          unfold
            nb078AlphaDummy393;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0390)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy394 g) from (by
          unfold
            nb078AlphaDummy394;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0391
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy389), (nb078AlphaDummy392 g)), ((nb078AlphaDummy388),
        (nb078AlphaDummy391 g)), ((nb078AlphaDummy387), (nb078AlphaDummy390 g)),
        ((nb078AlphaDummy385), (nb078AlphaDummy386 g)), ((nb078AlphaDummy381),
        (nb078AlphaDummy383 g)), ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
        ((nb078AlphaDummy374), (nb078AlphaDummy376 g)), ((nb078AlphaDummy373),
        (nb078AlphaDummy375 g)), ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
        ((nb078AlphaDummy377), (nb078AlphaDummy378 g)), ((nb078AlphaDummy368),
        (nb078AlphaDummy370 g)), ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
        ((nb078AlphaDummy371), (nb078AlphaDummy372 g)), ((nb078AlphaDummy650),
        (nb078AlphaDummy652 g)), ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
        ((nb078AlphaDummy653), (nb078AlphaDummy654 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy381))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy383
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399) from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy399)
        from (by
          unfold
            nb078AlphaDummy399;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0396)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy400 g) from (by
          unfold
            nb078AlphaDummy400;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0397
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy388) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0394)
                  0)))) (show (nb078AlphaDummy391 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0395
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy381))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy383 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy389) ≠
        (nb078AlphaDummy401) from (by
          unfold
            nb078AlphaDummy401;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0400)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy402 g) from (by
          unfold
            nb078AlphaDummy402;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0401
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy389) ≠ (nb078AlphaDummy397)
        from (by
          unfold
            nb078AlphaDummy397;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0398)
                  0)))) (show (nb078AlphaDummy392 g) ≠ (nb078AlphaDummy398 g) from (by
          unfold
            nb078AlphaDummy398;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0399
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from (by
                                        unfold nb078AlphaDummy385;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0382)
                                                0)))) (show (nb078AlphaDummy383 g) ≠
                                        (nb078AlphaDummy386 g) from (by
                                        unfold nb078AlphaDummy386;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0383 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy381) ≠ (nb078AlphaDummy385) from
                                        (by
                                          unfold nb078AlphaDummy385;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0382)
                                                  0)))) (show (nb078AlphaDummy383 g) ≠
        (nb078AlphaDummy386 g) from (by
                                          unfold nb078AlphaDummy386;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0383 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy385), (nb078AlphaDummy386 g)),
                                      ((nb078AlphaDummy381), (nb078AlphaDummy383 g)),
                                      ((nb078AlphaDummy382), (nb078AlphaDummy384 g)),
                                      ((nb078AlphaDummy374), (nb078AlphaDummy376 g)),
                                      ((nb078AlphaDummy373), (nb078AlphaDummy375 g)),
                                      ((nb078AlphaDummy379), (nb078AlphaDummy380 g)),
                                      ((nb078AlphaDummy377), (nb078AlphaDummy378 g)),
                                      ((nb078AlphaDummy368), (nb078AlphaDummy370 g)),
                                      ((nb078AlphaDummy367), (nb078AlphaDummy369 g)),
                                      ((nb078AlphaDummy371), (nb078AlphaDummy372 g)),
                                      ((nb078AlphaDummy650), (nb078AlphaDummy652 g)),
                                      ((nb078AlphaDummy649), (nb078AlphaDummy651 g)),
                                      ((nb078AlphaDummy653), (nb078AlphaDummy654 g)),
                                      ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
