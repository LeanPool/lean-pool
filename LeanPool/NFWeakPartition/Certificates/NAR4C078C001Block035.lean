/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block034

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part107`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0082`. -/
@[expose]
noncomputable def nb078SplitAlpha0082 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy583))
          (Class.cab (nb078AlphaDummy577)
            (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy577))
                (synCphi (Class.cv (nb078AlphaDummy578))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy583)) (Class.cab (nb078AlphaDummy577)
              (synWrex (nb078AlphaDummy578) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy577))
                  (synCphi (Class.cv (nb078AlphaDummy578)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy584 g))
          (Class.cab (nb078AlphaDummy579 g)
            (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                (synCphi (Class.cv (nb078AlphaDummy580 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy584 g))
            (Class.cab (nb078AlphaDummy579 g)
              (synWrex (nb078AlphaDummy580 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
                  (synCphi (Class.cv (nb078AlphaDummy580 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy578) from
                    (by
                      unfold nb078AlphaDummy578;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
                  (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy580 g) from (by
                      unfold nb078AlphaDummy580;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy577) from
                      (by
                        unfold nb078AlphaDummy577;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
                    (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy579 g) from (by
                        unfold nb078AlphaDummy579;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0594 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy583) from (by
                          unfold nb078AlphaDummy583;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0596) 0))))
                      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy584 g) from (by
                          unfold nb078AlphaDummy584;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0597 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy581) from (by
                            unfold nb078AlphaDummy581;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0593) 0))))
                        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy582 g) from (by
                            unfold nb078AlphaDummy582;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0595 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                              ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy569))).fv ∪
                      ((Class.cv (nb078AlphaDummy570))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy578) ≠ (nb078AlphaDummy585) from (by
                              unfold nb078AlphaDummy585;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0598) 0))))
                          (show (nb078AlphaDummy580 g) ≠ (nb078AlphaDummy587 g) from (by
                              unfold nb078AlphaDummy587;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0599 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy578) ≠ (nb078AlphaDummy586) from (by
                                unfold nb078AlphaDummy586;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0598) 1))))
                            (show (nb078AlphaDummy580 g) ≠ (nb078AlphaDummy588 g) from (by
                                unfold nb078AlphaDummy588;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0599 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy578))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy580 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy592) from (by
          unfold nb078AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 1)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy595 g) from (by
          unfold nb078AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy585) ≠ (nb078AlphaDummy591) from (by
          unfold nb078AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy594 g) from (by
          unfold nb078AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy578), (nb078AlphaDummy580 g)), ((nb078AlphaDummy577),
        (nb078AlphaDummy579 g)), ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy599)
        from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy599)
        from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy578), (nb078AlphaDummy580 g)), ((nb078AlphaDummy577),
        (nb078AlphaDummy579 g)), ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠
        (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy603)
        from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
                                        unfold nb078AlphaDummy589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078AlphaDummy587 g) ≠
                                        (nb078AlphaDummy590 g) from (by
                                        unfold nb078AlphaDummy590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
                                    ((nb078AlphaDummy585), (nb078AlphaDummy587 g)),
                                    ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
                                    ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
                                    ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
                                    ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
                                    ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from
                                    (by
                                      unfold nb078AlphaDummy589;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0600)
                                              0)))) (show
                                    (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy590 g) from
                                    (by
                                      unfold nb078AlphaDummy590;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0601 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
                                        unfold nb078AlphaDummy589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078AlphaDummy587 g) ≠
                                        (nb078AlphaDummy590 g) from (by
                                        unfold nb078AlphaDummy590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
                                    ((nb078AlphaDummy585), (nb078AlphaDummy587 g)),
                                    ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
                                    ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
                                    ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
                                    ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
                                    ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy578) from
                      (by
                        unfold nb078AlphaDummy578;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
                    (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy580 g) from (by
                        unfold nb078AlphaDummy580;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0594 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy577) from (by
                          unfold nb078AlphaDummy577;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0592) 0))))
                      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy579 g) from (by
                          unfold nb078AlphaDummy579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy583) from (by
                            unfold nb078AlphaDummy583;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0596) 0))))
                        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy584 g) from (by
                            unfold nb078AlphaDummy584;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0597 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy581) from (by
                              unfold nb078AlphaDummy581;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0593) 0))))
                          (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy582 g) from (by
                              unfold nb078AlphaDummy582;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0595 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                                ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy569))).fv ∪
                        ((Class.cv (nb078AlphaDummy570))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy578) ≠ (nb078AlphaDummy585) from (by
                                unfold nb078AlphaDummy585;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0598) 0))))
                            (show (nb078AlphaDummy580 g) ≠ (nb078AlphaDummy587 g) from (by
                                unfold nb078AlphaDummy587;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0599 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy578) ≠ (nb078AlphaDummy586) from (by
                                  unfold nb078AlphaDummy586;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0598) 1))))
                              (show (nb078AlphaDummy580 g) ≠ (nb078AlphaDummy588 g) from
                                (by
                                  unfold nb078AlphaDummy588;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0599 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy578))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy580 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy585) ≠ (nb078AlphaDummy592) from (by
          unfold nb078AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 1)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy595 g) from (by
          unfold nb078AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy585) ≠ (nb078AlphaDummy591) from (by
          unfold nb078AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy594 g) from (by
          unfold nb078AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589)
        from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy578), (nb078AlphaDummy580 g)), ((nb078AlphaDummy577),
        (nb078AlphaDummy579 g)), ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy599)
        from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy599)
        from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy578), (nb078AlphaDummy580 g)), ((nb078AlphaDummy577),
        (nb078AlphaDummy579 g)), ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)), ((nb078AlphaDummy570),
        (nb078AlphaDummy573 g)), ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠
        (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy603)
        from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from
                                        (by
                                          unfold nb078AlphaDummy589;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0600)
                                                  0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
                                          unfold nb078AlphaDummy590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0601 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
                                      ((nb078AlphaDummy585), (nb078AlphaDummy587 g)),
                                      ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
                                      ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
                                      ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
                                      ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
                                      ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
                                        unfold nb078AlphaDummy589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078AlphaDummy587 g) ≠
                                        (nb078AlphaDummy590 g) from (by
                                        unfold nb078AlphaDummy590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from
                                        (by
                                          unfold nb078AlphaDummy589;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0600)
                                                  0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
                                          unfold nb078AlphaDummy590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0601 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
                                      ((nb078AlphaDummy585), (nb078AlphaDummy587 g)),
                                      ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
                                      ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
                                      ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
                                      ((nb078AlphaDummy583), (nb078AlphaDummy584 g)),
                                      ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
                                      ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                      ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                      ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part108`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0083`. -/
@[expose]
noncomputable def nb078SplitAlpha0083 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
        ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
        ((nb078AlphaDummy607), (nb078AlphaDummy608 g)),
        ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy578))
          (Class.cv (nb078AlphaDummy570))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy577))
            (synCun (synCphi (Class.cv (nb078AlphaDummy578))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy580 g))
          (Class.cv (nb078AlphaDummy573 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy579 g))
            (synCun (synCphi (Class.cv (nb078AlphaDummy580 g))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy578) from (by
              unfold nb078AlphaDummy578;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
          (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy580 g) from (by
              unfold nb078AlphaDummy580;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy577) from (by
                unfold nb078AlphaDummy577;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
            (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy579 g) from (by
                unfold nb078AlphaDummy579;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy607) from (by
                  unfold nb078AlphaDummy607;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0624) 0))))
              (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy608 g) from (by
                  unfold nb078AlphaDummy608;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0625 g) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy570) ≠ (nb078AlphaDummy581) from (by
                    unfold nb078AlphaDummy581;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0621) 0))))
                (show (nb078AlphaDummy573 g) ≠ (nb078AlphaDummy582 g) from (by
                    unfold nb078AlphaDummy582;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0623 g) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy569))).fv ∪
                ((Class.cv (nb078AlphaDummy570))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                ((Class.cv (nb078AlphaDummy573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy578) ≠ (nb078AlphaDummy585) from (by
                                        unfold nb078AlphaDummy585;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0598)
                                                0)))) (show (nb078AlphaDummy580 g) ≠
                                        (nb078AlphaDummy587 g) from (by
                                        unfold nb078AlphaDummy587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0599 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy578) ≠ (nb078AlphaDummy586) from
                                        (by
                                          unfold nb078AlphaDummy586;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0598)
                                                  1)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy588 g) from (by
                                          unfold nb078AlphaDummy588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0599 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy578) ≠
        (nb078AlphaDummy611) from (by
          unfold nb078AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0628) 0)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy612 g) from (by
          unfold nb078AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0629 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy578) ≠ (nb078AlphaDummy609) from (by
          unfold nb078AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0626) 0)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy610 g) from (by
          unfold nb078AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0627 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy578))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy580 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy592) from (by
          unfold nb078AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  1)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy595 g) from (by
          unfold nb078AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy591)
        from (by
          unfold nb078AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  0)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy594 g) from (by
          unfold nb078AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589)
        from (by
          unfold
            nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy590 g) from (by
          unfold
            nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy611), (nb078AlphaDummy612 g)), ((nb078AlphaDummy609),
        (nb078AlphaDummy610 g)), ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
        ((nb078AlphaDummy577), (nb078AlphaDummy579 g)), ((nb078AlphaDummy607),
        (nb078AlphaDummy608 g)), ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy611), (nb078AlphaDummy612 g)), ((nb078AlphaDummy609),
        (nb078AlphaDummy610 g)), ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
        ((nb078AlphaDummy577), (nb078AlphaDummy579 g)), ((nb078AlphaDummy607),
        (nb078AlphaDummy608 g)), ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠
        (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589)
        from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
        ((nb078AlphaDummy585), (nb078AlphaDummy587 g)), ((nb078AlphaDummy586),
        (nb078AlphaDummy588 g)), ((nb078AlphaDummy611), (nb078AlphaDummy612 g)),
        ((nb078AlphaDummy609), (nb078AlphaDummy610 g)), ((nb078AlphaDummy578),
        (nb078AlphaDummy580 g)), ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
        ((nb078AlphaDummy607), (nb078AlphaDummy608 g)), ((nb078AlphaDummy581),
        (nb078AlphaDummy582 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
        ((nb078AlphaDummy585), (nb078AlphaDummy587 g)), ((nb078AlphaDummy586),
        (nb078AlphaDummy588 g)), ((nb078AlphaDummy611), (nb078AlphaDummy612 g)),
        ((nb078AlphaDummy609), (nb078AlphaDummy610 g)), ((nb078AlphaDummy578),
        (nb078AlphaDummy580 g)), ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
        ((nb078AlphaDummy607), (nb078AlphaDummy608 g)), ((nb078AlphaDummy581),
        (nb078AlphaDummy582 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy578) ≠ (nb078AlphaDummy585) from (by
                                        unfold nb078AlphaDummy585;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0598)
                                                0)))) (show (nb078AlphaDummy580 g) ≠
                                        (nb078AlphaDummy587 g) from (by
                                        unfold nb078AlphaDummy587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0599 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy578) ≠ (nb078AlphaDummy586) from
                                        (by
                                          unfold nb078AlphaDummy586;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0598)
                                                  1)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy588 g) from (by
                                          unfold nb078AlphaDummy588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0599 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy578) ≠
        (nb078AlphaDummy611) from (by
          unfold nb078AlphaDummy611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0628) 0)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy612 g) from (by
          unfold nb078AlphaDummy612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0629 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy578) ≠ (nb078AlphaDummy609) from (by
          unfold nb078AlphaDummy609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0626) 0)))) (show (nb078AlphaDummy580 g) ≠
        (nb078AlphaDummy610 g) from (by
          unfold nb078AlphaDummy610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0627 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy578))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy580 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy592) from (by
          unfold nb078AlphaDummy592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  1)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy595 g) from (by
          unfold nb078AlphaDummy595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy591)
        from (by
          unfold nb078AlphaDummy591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  0)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy594 g) from (by
          unfold nb078AlphaDummy594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589)
        from (by
          unfold
            nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078AlphaDummy587 g) ≠ (nb078AlphaDummy590 g) from (by
          unfold
            nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy611), (nb078AlphaDummy612 g)), ((nb078AlphaDummy609),
        (nb078AlphaDummy610 g)), ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
        ((nb078AlphaDummy577), (nb078AlphaDummy579 g)), ((nb078AlphaDummy607),
        (nb078AlphaDummy608 g)), ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy599) from (by
          unfold
            nb078AlphaDummy599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy600 g) from (by
          unfold
            nb078AlphaDummy600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy597)
        from (by
          unfold
            nb078AlphaDummy597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy598 g) from (by
          unfold
            nb078AlphaDummy598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy593), (nb078AlphaDummy596 g)), ((nb078AlphaDummy592),
        (nb078AlphaDummy595 g)), ((nb078AlphaDummy591), (nb078AlphaDummy594 g)),
        ((nb078AlphaDummy589), (nb078AlphaDummy590 g)), ((nb078AlphaDummy585),
        (nb078AlphaDummy587 g)), ((nb078AlphaDummy586), (nb078AlphaDummy588 g)),
        ((nb078AlphaDummy611), (nb078AlphaDummy612 g)), ((nb078AlphaDummy609),
        (nb078AlphaDummy610 g)), ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
        ((nb078AlphaDummy577), (nb078AlphaDummy579 g)), ((nb078AlphaDummy607),
        (nb078AlphaDummy608 g)), ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)), ((nb078AlphaDummy569),
        (nb078AlphaDummy572 g)), ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy587 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy585))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy592) ≠
        (nb078AlphaDummy603) from (by
          unfold
            nb078AlphaDummy603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy604 g) from (by
          unfold
            nb078AlphaDummy604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy592) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078AlphaDummy595 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy585))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy587 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy593) ≠
        (nb078AlphaDummy605) from (by
          unfold
            nb078AlphaDummy605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy606 g) from (by
          unfold
            nb078AlphaDummy606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy593) ≠ (nb078AlphaDummy601)
        from (by
          unfold
            nb078AlphaDummy601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078AlphaDummy596 g) ≠ (nb078AlphaDummy602 g) from (by
          unfold
            nb078AlphaDummy602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589)
        from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
        ((nb078AlphaDummy585), (nb078AlphaDummy587 g)), ((nb078AlphaDummy586),
        (nb078AlphaDummy588 g)), ((nb078AlphaDummy611), (nb078AlphaDummy612 g)),
        ((nb078AlphaDummy609), (nb078AlphaDummy610 g)), ((nb078AlphaDummy578),
        (nb078AlphaDummy580 g)), ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
        ((nb078AlphaDummy607), (nb078AlphaDummy608 g)), ((nb078AlphaDummy581),
        (nb078AlphaDummy582 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy585) ≠ (nb078AlphaDummy589) from (by
          unfold nb078AlphaDummy589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078AlphaDummy587 g) ≠
        (nb078AlphaDummy590 g) from (by
          unfold nb078AlphaDummy590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy589), (nb078AlphaDummy590 g)),
        ((nb078AlphaDummy585), (nb078AlphaDummy587 g)), ((nb078AlphaDummy586),
        (nb078AlphaDummy588 g)), ((nb078AlphaDummy611), (nb078AlphaDummy612 g)),
        ((nb078AlphaDummy609), (nb078AlphaDummy610 g)), ((nb078AlphaDummy578),
        (nb078AlphaDummy580 g)), ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
        ((nb078AlphaDummy607), (nb078AlphaDummy608 g)), ((nb078AlphaDummy581),
        (nb078AlphaDummy582 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy609), (nb078AlphaDummy610 g)),
                    ((nb078AlphaDummy578), (nb078AlphaDummy580 g)),
                    ((nb078AlphaDummy577), (nb078AlphaDummy579 g)),
                    ((nb078AlphaDummy607), (nb078AlphaDummy608 g)),
                    ((nb078AlphaDummy581), (nb078AlphaDummy582 g)),
                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part109`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0084`. -/
@[expose]
noncomputable def nb078SplitAlpha0084 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
        ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
        ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
        ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy619))
          (Class.cab (nb078AlphaDummy613)
            (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
              (Wff.classEq (Class.cv (nb078AlphaDummy613))
                (synCphi (Class.cv (nb078AlphaDummy614))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy619)) (Class.cab (nb078AlphaDummy613)
              (synWrex (nb078AlphaDummy614) (Class.cv (nb078AlphaDummy569))
                (Wff.classEq (Class.cv (nb078AlphaDummy613))
                  (synCphi (Class.cv (nb078AlphaDummy614)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy620 g))
          (Class.cab (nb078AlphaDummy615 g)
            (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
              (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                (synCphi (Class.cv (nb078AlphaDummy616 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy620 g))
            (Class.cab (nb078AlphaDummy615 g)
              (synWrex (nb078AlphaDummy616 g) (Class.cv (nb078AlphaDummy572 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy615 g))
                  (synCphi (Class.cv (nb078AlphaDummy616 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy614) from
                    (by
                      unfold nb078AlphaDummy614;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
                  (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy616 g) from (by
                      unfold nb078AlphaDummy616;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
                  (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy613) from
                      (by
                        unfold nb078AlphaDummy613;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
                    (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy615 g) from (by
                        unfold nb078AlphaDummy615;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0632 g) 0)))) (TAlphaVar.there
                      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy619) from (by
                          unfold nb078AlphaDummy619;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0634) 0))))
                      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy620 g) from (by
                          unfold nb078AlphaDummy620;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0635 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy617) from (by
                            unfold nb078AlphaDummy617;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0631) 0))))
                        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy618 g) from (by
                            unfold nb078AlphaDummy618;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0633 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                  (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                            (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                              ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                                ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy569))).fv ∪
                      ((Class.cv (nb078AlphaDummy571))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                      ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy621) from (by
                              unfold nb078AlphaDummy621;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                          (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy623 g) from (by
                              unfold nb078AlphaDummy623;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy622) from (by
                                unfold nb078AlphaDummy622;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                            (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy624 g) from (by
                                unfold nb078AlphaDummy624;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078AlphaDummy614))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy616 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy621) ≠ (nb078AlphaDummy628) from (by
          unfold nb078AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy631 g) from (by
          unfold nb078AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy627) from (by
          unfold nb078AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy630 g) from (by
          unfold nb078AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
          unfold nb078AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638) 0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
          unfold nb078AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy614), (nb078AlphaDummy616 g)), ((nb078AlphaDummy613),
        (nb078AlphaDummy615 g)), ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy614), (nb078AlphaDummy616 g)), ((nb078AlphaDummy613),
        (nb078AlphaDummy615 g)), ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy623
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639) from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639)
        from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠
        (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
                                        unfold nb078AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078AlphaDummy623 g) ≠
                                        (nb078AlphaDummy626 g) from (by
                                        unfold nb078AlphaDummy626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                    ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                    ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                    ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                    ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                    ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
                                    ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
                                    ((nb078AlphaDummy571), (nb078AlphaDummy574 g)),
                                    ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
                                    ((nb078AlphaDummy569), (nb078AlphaDummy572 g)),
                                    ((nb078AlphaDummy575), (nb078AlphaDummy576 g)),
                                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                                    ((nb078AlphaDummy003), x)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                    (by
                                      unfold nb078AlphaDummy625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078AlphaDummy623 g) ≠ (nb078AlphaDummy626 g) from
                                    (by
                                      unfold nb078AlphaDummy626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
                                        unfold nb078AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078AlphaDummy623 g) ≠
                                        (nb078AlphaDummy626 g) from (by
                                        unfold nb078AlphaDummy626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                    ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                    ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                    ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                    ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                    ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
                                    ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
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
                  (TAlphaVar.there (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy614) from
                      (by
                        unfold nb078AlphaDummy614;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
                    (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy616 g) from (by
                        unfold nb078AlphaDummy616;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0632 g) 1)))) (TAlphaVar.there
                      (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy613) from (by
                          unfold nb078AlphaDummy613;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0630) 0))))
                      (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy615 g) from (by
                          unfold nb078AlphaDummy615;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
                      (TAlphaVar.there
                        (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy619) from (by
                            unfold nb078AlphaDummy619;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0634) 0))))
                        (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy620 g) from (by
                            unfold nb078AlphaDummy620;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0635 g) 0))))
                        (TAlphaVar.there
                          (show (nb078AlphaDummy569) ≠ (nb078AlphaDummy617) from (by
                              unfold nb078AlphaDummy617;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0631) 0))))
                          (show (nb078AlphaDummy572 g) ≠ (nb078AlphaDummy618 g) from (by
                              unfold nb078AlphaDummy618;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0633 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                    (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                                ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCcnv
                                      (synCcnv (Class.cv (nb078AlphaDummy001))))).fv)
                                (by decide)) (freshVar_injective (((synCcnv (Class.cv g))).fv ∪
                                  ((synCcnv (synCcnv (Class.cv g)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078AlphaDummy569))).fv ∪
                        ((Class.cv (nb078AlphaDummy571))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078AlphaDummy572 g))).fv ∪
                        ((Class.cv (nb078AlphaDummy574 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy621) from (by
                                unfold nb078AlphaDummy621;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                            (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy623 g) from (by
                                unfold nb078AlphaDummy623;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy614) ≠ (nb078AlphaDummy622) from (by
                                  unfold nb078AlphaDummy622;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                              (show (nb078AlphaDummy616 g) ≠ (nb078AlphaDummy624 g) from
                                (by
                                  unfold nb078AlphaDummy624;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy614))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy616 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy628) from (by
          unfold nb078AlphaDummy628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy631 g) from (by
          unfold nb078AlphaDummy631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy621) ≠ (nb078AlphaDummy627) from (by
          unfold nb078AlphaDummy627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy630 g) from (by
          unfold nb078AlphaDummy630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy621) ≠ (nb078AlphaDummy625)
        from (by
          unfold nb078AlphaDummy625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638)
                  0)))) (show (nb078AlphaDummy623 g) ≠ (nb078AlphaDummy626 g) from (by
          unfold nb078AlphaDummy626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy614), (nb078AlphaDummy616 g)), ((nb078AlphaDummy613),
        (nb078AlphaDummy615 g)), ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy635) from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy635)
        from (by
          unfold
            nb078AlphaDummy635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy636 g) from (by
          unfold
            nb078AlphaDummy636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy633)
        from (by
          unfold
            nb078AlphaDummy633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy634 g) from (by
          unfold
            nb078AlphaDummy634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy629), (nb078AlphaDummy632 g)), ((nb078AlphaDummy628),
        (nb078AlphaDummy631 g)), ((nb078AlphaDummy627), (nb078AlphaDummy630 g)),
        ((nb078AlphaDummy625), (nb078AlphaDummy626 g)), ((nb078AlphaDummy621),
        (nb078AlphaDummy623 g)), ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
        ((nb078AlphaDummy614), (nb078AlphaDummy616 g)), ((nb078AlphaDummy613),
        (nb078AlphaDummy615 g)), ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
        ((nb078AlphaDummy617), (nb078AlphaDummy618 g)), ((nb078AlphaDummy571),
        (nb078AlphaDummy574 g)), ((nb078AlphaDummy570), (nb078AlphaDummy573 g)),
        ((nb078AlphaDummy569), (nb078AlphaDummy572 g)), ((nb078AlphaDummy575),
        (nb078AlphaDummy576 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy621))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy623
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639) from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy639)
        from (by
          unfold
            nb078AlphaDummy639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy640 g) from (by
          unfold
            nb078AlphaDummy640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy628) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078AlphaDummy631 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy621))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy623 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy629) ≠
        (nb078AlphaDummy641) from (by
          unfold
            nb078AlphaDummy641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy642 g) from (by
          unfold
            nb078AlphaDummy642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy629) ≠ (nb078AlphaDummy637)
        from (by
          unfold
            nb078AlphaDummy637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078AlphaDummy632 g) ≠ (nb078AlphaDummy638 g) from (by
          unfold
            nb078AlphaDummy638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
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
                                      (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from (by
                                        unfold nb078AlphaDummy625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078AlphaDummy623 g) ≠
                                        (nb078AlphaDummy626 g) from (by
                                        unfold nb078AlphaDummy626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy621) ≠ (nb078AlphaDummy625) from
                                        (by
                                          unfold nb078AlphaDummy625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078AlphaDummy623 g) ≠
        (nb078AlphaDummy626 g) from (by
                                          unfold nb078AlphaDummy626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy625), (nb078AlphaDummy626 g)),
                                      ((nb078AlphaDummy621), (nb078AlphaDummy623 g)),
                                      ((nb078AlphaDummy622), (nb078AlphaDummy624 g)),
                                      ((nb078AlphaDummy614), (nb078AlphaDummy616 g)),
                                      ((nb078AlphaDummy613), (nb078AlphaDummy615 g)),
                                      ((nb078AlphaDummy619), (nb078AlphaDummy620 g)),
                                      ((nb078AlphaDummy617), (nb078AlphaDummy618 g)),
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
