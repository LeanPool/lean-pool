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

@[expose]
noncomputable def nb078_split_alpha_0082 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_583))
          (Class.cab (nb078_alpha_dummy_577)
            (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                (syn_cphi (Class.cv (nb078_alpha_dummy_578))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_583)) (Class.cab (nb078_alpha_dummy_577)
              (syn_wrex (nb078_alpha_dummy_578) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_578)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_584 g))
          (Class.cab (nb078_alpha_dummy_579 g)
            (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_584 g))
            (Class.cab (nb078_alpha_dummy_579 g)
              (syn_wrex (nb078_alpha_dummy_580 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_578) from
                    (by
                      unfold nb078_alpha_dummy_578;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
                  (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_580 g) from (by
                      unfold nb078_alpha_dummy_580;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0594 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_577) from
                      (by
                        unfold nb078_alpha_dummy_577;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 0))))
                    (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_579 g) from (by
                        unfold nb078_alpha_dummy_579;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0594 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_583) from (by
                          unfold nb078_alpha_dummy_583;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0596) 0))))
                      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_584 g) from (by
                          unfold nb078_alpha_dummy_584;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0597 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_581) from (by
                            unfold nb078_alpha_dummy_581;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0593) 0))))
                        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_582 g) from (by
                            unfold nb078_alpha_dummy_582;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0595 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_585) from (by
                              unfold nb078_alpha_dummy_585;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0598) 0))))
                          (show (nb078_alpha_dummy_580 g) ≠ (nb078_alpha_dummy_587 g) from (by
                              unfold nb078_alpha_dummy_587;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0599 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_586) from (by
                                unfold nb078_alpha_dummy_586;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0598) 1))))
                            (show (nb078_alpha_dummy_580 g) ≠ (nb078_alpha_dummy_588 g) from (by
                                unfold nb078_alpha_dummy_588;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0599 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_580 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_592) from (by
          unfold nb078_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 1)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_595 g) from (by
          unfold nb078_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_591) from (by
          unfold nb078_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_594 g) from (by
          unfold nb078_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577),
        (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_599)
        from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_599)
        from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577),
        (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠
        (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_603)
        from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
                                        unfold nb078_alpha_dummy_589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078_alpha_dummy_587 g) ≠
                                        (nb078_alpha_dummy_590 g) from (by
                                        unfold nb078_alpha_dummy_590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
                                    ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)),
                                    ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
                                    ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
                                    ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
                                    ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
                                    ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from
                                    (by
                                      unfold nb078_alpha_dummy_589;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0600)
                                              0)))) (show
                                    (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_590 g) from
                                    (by
                                      unfold nb078_alpha_dummy_590;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0601 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
                                        unfold nb078_alpha_dummy_589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078_alpha_dummy_587 g) ≠
                                        (nb078_alpha_dummy_590 g) from (by
                                        unfold nb078_alpha_dummy_590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
                                    ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)),
                                    ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
                                    ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
                                    ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
                                    ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
                                    ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_578) from
                      (by
                        unfold nb078_alpha_dummy_578;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0592) 1))))
                    (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_580 g) from (by
                        unfold nb078_alpha_dummy_580;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0594 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_577) from (by
                          unfold nb078_alpha_dummy_577;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0592) 0))))
                      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_579 g) from (by
                          unfold nb078_alpha_dummy_579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0594 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_583) from (by
                            unfold nb078_alpha_dummy_583;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0596) 0))))
                        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_584 g) from (by
                            unfold nb078_alpha_dummy_584;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0597 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_581) from (by
                              unfold nb078_alpha_dummy_581;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0593) 0))))
                          (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_582 g) from (by
                              unfold nb078_alpha_dummy_582;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0595 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_585) from (by
                                unfold nb078_alpha_dummy_585;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0598) 0))))
                            (show (nb078_alpha_dummy_580 g) ≠ (nb078_alpha_dummy_587 g) from (by
                                unfold nb078_alpha_dummy_587;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0599 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_586) from (by
                                  unfold nb078_alpha_dummy_586;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0598) 1))))
                              (show (nb078_alpha_dummy_580 g) ≠ (nb078_alpha_dummy_588 g) from
                                (by
                                  unfold nb078_alpha_dummy_588;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0599 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_578))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_592) from (by
          unfold nb078_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 1)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_595 g) from (by
          unfold nb078_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_591) from (by
          unfold nb078_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_594 g) from (by
          unfold nb078_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589)
        from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577),
        (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_599)
        from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_599)
        from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577),
        (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠
        (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_603)
        from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from
                                        (by
                                          unfold nb078_alpha_dummy_589;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0600)
                                                  0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
                                          unfold nb078_alpha_dummy_590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0601 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
                                      ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)),
                                      ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
                                      ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
                                      ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
                                      ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
                                      ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
                                        unfold nb078_alpha_dummy_589;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0600)
                                                0)))) (show (nb078_alpha_dummy_587 g) ≠
                                        (nb078_alpha_dummy_590 g) from (by
                                        unfold nb078_alpha_dummy_590;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0601 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from
                                        (by
                                          unfold nb078_alpha_dummy_589;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0600)
                                                  0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
                                          unfold nb078_alpha_dummy_590;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0601 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
                                      ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)),
                                      ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
                                      ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
                                      ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
                                      ((nb078_alpha_dummy_583), (nb078_alpha_dummy_584 g)),
                                      ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
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

@[expose]
noncomputable def nb078_split_alpha_0083 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
        ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
        ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)),
        ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_578))
          (Class.cv (nb078_alpha_dummy_570))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_577))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_578))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_580 g))
          (Class.cv (nb078_alpha_dummy_573 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_579 g))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_580 g))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_578) from (by
              unfold nb078_alpha_dummy_578;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 1))))
          (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_580 g) from (by
              unfold nb078_alpha_dummy_580;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_577) from (by
                unfold nb078_alpha_dummy_577;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0620) 0))))
            (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_579 g) from (by
                unfold nb078_alpha_dummy_579;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0622 g) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_607) from (by
                  unfold nb078_alpha_dummy_607;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0624) 0))))
              (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_608 g) from (by
                  unfold nb078_alpha_dummy_608;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0625 g) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_581) from (by
                    unfold nb078_alpha_dummy_581;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0621) 0))))
                (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_582 g) from (by
                    unfold nb078_alpha_dummy_582;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0623 g) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_585) from (by
                                        unfold nb078_alpha_dummy_585;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0598)
                                                0)))) (show (nb078_alpha_dummy_580 g) ≠
                                        (nb078_alpha_dummy_587 g) from (by
                                        unfold nb078_alpha_dummy_587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0599 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_586) from
                                        (by
                                          unfold nb078_alpha_dummy_586;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0598)
                                                  1)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_588 g) from (by
                                          unfold nb078_alpha_dummy_588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0599 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_578) ≠
        (nb078_alpha_dummy_611) from (by
          unfold nb078_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0628) 0)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_612 g) from (by
          unfold nb078_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0629 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_609) from (by
          unfold nb078_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0626) 0)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_610 g) from (by
          unfold nb078_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0627 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_592) from (by
          unfold nb078_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  1)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_595 g) from (by
          unfold nb078_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_591)
        from (by
          unfold nb078_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  0)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_594 g) from (by
          unfold nb078_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589)
        from (by
          unfold
            nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_590 g) from (by
          unfold
            nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609),
        (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
        ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607),
        (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609),
        (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
        ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607),
        (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠
        (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589)
        from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
        ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586),
        (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)),
        ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578),
        (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
        ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581),
        (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
        ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586),
        (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)),
        ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578),
        (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
        ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581),
        (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_585) from (by
                                        unfold nb078_alpha_dummy_585;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0598)
                                                0)))) (show (nb078_alpha_dummy_580 g) ≠
                                        (nb078_alpha_dummy_587 g) from (by
                                        unfold nb078_alpha_dummy_587;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0599 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_586) from
                                        (by
                                          unfold nb078_alpha_dummy_586;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0598)
                                                  1)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_588 g) from (by
                                          unfold nb078_alpha_dummy_588;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0599 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_578) ≠
        (nb078_alpha_dummy_611) from (by
          unfold nb078_alpha_dummy_611;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0628) 0)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_612 g) from (by
          unfold nb078_alpha_dummy_612;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0629 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_578) ≠ (nb078_alpha_dummy_609) from (by
          unfold nb078_alpha_dummy_609;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0626) 0)))) (show (nb078_alpha_dummy_580 g) ≠
        (nb078_alpha_dummy_610 g) from (by
          unfold nb078_alpha_dummy_610;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0627 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_578))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_580 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_592) from (by
          unfold nb078_alpha_dummy_592;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  1)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_595 g) from (by
          unfold nb078_alpha_dummy_595;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_591)
        from (by
          unfold nb078_alpha_dummy_591;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0602)
                  0)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_594 g) from (by
          unfold nb078_alpha_dummy_594;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0603
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589)
        from (by
          unfold
            nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600)
                  0)))) (show (nb078_alpha_dummy_587 g) ≠ (nb078_alpha_dummy_590 g) from (by
          unfold
            nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609),
        (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
        ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607),
        (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0606)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0607
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0604)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0605
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_599) from (by
          unfold
            nb078_alpha_dummy_599;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0610)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_600 g) from (by
          unfold
            nb078_alpha_dummy_600;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0611
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_597)
        from (by
          unfold
            nb078_alpha_dummy_597;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0608)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_598 g) from (by
          unfold
            nb078_alpha_dummy_598;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0609
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_593), (nb078_alpha_dummy_596 g)), ((nb078_alpha_dummy_592),
        (nb078_alpha_dummy_595 g)), ((nb078_alpha_dummy_591), (nb078_alpha_dummy_594 g)),
        ((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)), ((nb078_alpha_dummy_585),
        (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586), (nb078_alpha_dummy_588 g)),
        ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)), ((nb078_alpha_dummy_609),
        (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
        ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)), ((nb078_alpha_dummy_607),
        (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_585))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠
        (nb078_alpha_dummy_603) from (by
          unfold
            nb078_alpha_dummy_603;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0614)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_604 g) from (by
          unfold
            nb078_alpha_dummy_604;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0615
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_592) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0612)
                  0)))) (show (nb078_alpha_dummy_595 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0613
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_585))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_587 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠
        (nb078_alpha_dummy_605) from (by
          unfold
            nb078_alpha_dummy_605;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0618)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_606 g) from (by
          unfold
            nb078_alpha_dummy_606;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0619
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_593) ≠ (nb078_alpha_dummy_601)
        from (by
          unfold
            nb078_alpha_dummy_601;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0616)
                  0)))) (show (nb078_alpha_dummy_596 g) ≠ (nb078_alpha_dummy_602 g) from (by
          unfold
            nb078_alpha_dummy_602;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0617
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589)
        from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
        ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586),
        (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)),
        ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578),
        (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
        ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581),
        (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc])))))
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_585) ≠ (nb078_alpha_dummy_589) from (by
          unfold nb078_alpha_dummy_589;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0600) 0)))) (show (nb078_alpha_dummy_587 g) ≠
        (nb078_alpha_dummy_590 g) from (by
          unfold nb078_alpha_dummy_590;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0601 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_589), (nb078_alpha_dummy_590 g)),
        ((nb078_alpha_dummy_585), (nb078_alpha_dummy_587 g)), ((nb078_alpha_dummy_586),
        (nb078_alpha_dummy_588 g)), ((nb078_alpha_dummy_611), (nb078_alpha_dummy_612 g)),
        ((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)), ((nb078_alpha_dummy_578),
        (nb078_alpha_dummy_580 g)), ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
        ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)), ((nb078_alpha_dummy_581),
        (nb078_alpha_dummy_582 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_609), (nb078_alpha_dummy_610 g)),
                    ((nb078_alpha_dummy_578), (nb078_alpha_dummy_580 g)),
                    ((nb078_alpha_dummy_577), (nb078_alpha_dummy_579 g)),
                    ((nb078_alpha_dummy_607), (nb078_alpha_dummy_608 g)),
                    ((nb078_alpha_dummy_581), (nb078_alpha_dummy_582 g)),
                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0084 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_619))
          (Class.cab (nb078_alpha_dummy_613)
            (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                (syn_cphi (Class.cv (nb078_alpha_dummy_614))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_619)) (Class.cab (nb078_alpha_dummy_613)
              (syn_wrex (nb078_alpha_dummy_614) (Class.cv (nb078_alpha_dummy_569))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_613))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_614)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_620 g))
          (Class.cab (nb078_alpha_dummy_615 g)
            (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_620 g))
            (Class.cab (nb078_alpha_dummy_615 g)
              (syn_wrex (nb078_alpha_dummy_616 g) (Class.cv (nb078_alpha_dummy_572 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_615 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_616 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_614) from
                    (by
                      unfold nb078_alpha_dummy_614;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
                  (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_616 g) from (by
                      unfold nb078_alpha_dummy_616;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0632 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_613) from
                      (by
                        unfold nb078_alpha_dummy_613;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 0))))
                    (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_615 g) from (by
                        unfold nb078_alpha_dummy_615;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0632 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_619) from (by
                          unfold nb078_alpha_dummy_619;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0634) 0))))
                      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_620 g) from (by
                          unfold nb078_alpha_dummy_620;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0635 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_617) from (by
                            unfold nb078_alpha_dummy_617;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0631) 0))))
                        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_618 g) from (by
                            unfold nb078_alpha_dummy_618;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0633 g) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_571))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_621) from (by
                              unfold nb078_alpha_dummy_621;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                          (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_623 g) from (by
                              unfold nb078_alpha_dummy_623;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_622) from (by
                                unfold nb078_alpha_dummy_622;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                            (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_624 g) from (by
                                unfold nb078_alpha_dummy_624;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_616 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_628) from (by
          unfold nb078_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_631 g) from (by
          unfold nb078_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_627) from (by
          unfold nb078_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_630 g) from (by
          unfold nb078_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
          unfold nb078_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_626 g) from (by
          unfold nb078_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613),
        (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613),
        (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639) from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639)
        from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠
        (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
                                        unfold nb078_alpha_dummy_625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078_alpha_dummy_623 g) ≠
                                        (nb078_alpha_dummy_626 g) from (by
                                        unfold nb078_alpha_dummy_626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                    ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                    ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                    ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                    ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                    ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
                                    ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                    (by
                                      unfold nb078_alpha_dummy_625;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0638)
                                              0)))) (show
                                    (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from
                                    (by
                                      unfold nb078_alpha_dummy_626;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0639 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
                                        unfold nb078_alpha_dummy_625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078_alpha_dummy_623 g) ≠
                                        (nb078_alpha_dummy_626 g) from (by
                                        unfold nb078_alpha_dummy_626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                    ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                    ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                    ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                    ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                    ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
                                    ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_614) from
                      (by
                        unfold nb078_alpha_dummy_614;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0630) 1))))
                    (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_616 g) from (by
                        unfold nb078_alpha_dummy_616;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0632 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_613) from (by
                          unfold nb078_alpha_dummy_613;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0630) 0))))
                      (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_615 g) from (by
                          unfold nb078_alpha_dummy_615;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0632 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_619) from (by
                            unfold nb078_alpha_dummy_619;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0634) 0))))
                        (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_620 g) from (by
                            unfold nb078_alpha_dummy_620;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0635 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_617) from (by
                              unfold nb078_alpha_dummy_617;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0631) 0))))
                          (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_618 g) from (by
                              unfold nb078_alpha_dummy_618;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0633 g) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv
                                      (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))).fv)
                                (by decide)) (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪
                                  ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_571))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_621) from (by
                                unfold nb078_alpha_dummy_621;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0636) 0))))
                            (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_623 g) from (by
                                unfold nb078_alpha_dummy_623;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0637 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_614) ≠ (nb078_alpha_dummy_622) from (by
                                  unfold nb078_alpha_dummy_622;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0636) 1))))
                              (show (nb078_alpha_dummy_616 g) ≠ (nb078_alpha_dummy_624 g) from
                                (by
                                  unfold nb078_alpha_dummy_624;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0637 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_614))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_616 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_628) from (by
          unfold nb078_alpha_dummy_628;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 1)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_631 g) from (by
          unfold nb078_alpha_dummy_631;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_627) from (by
          unfold nb078_alpha_dummy_627;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0640) 0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_630 g) from (by
          unfold nb078_alpha_dummy_630;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0641 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625)
        from (by
          unfold nb078_alpha_dummy_625;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0638)
                  0)))) (show (nb078_alpha_dummy_623 g) ≠ (nb078_alpha_dummy_626 g) from (by
          unfold nb078_alpha_dummy_626;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0639 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613),
        (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_635) from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0644)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0645
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0642)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0643
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_635)
        from (by
          unfold
            nb078_alpha_dummy_635;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0648)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_636 g) from (by
          unfold
            nb078_alpha_dummy_636;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0649
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_633)
        from (by
          unfold
            nb078_alpha_dummy_633;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0646)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_634 g) from (by
          unfold
            nb078_alpha_dummy_634;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0647
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_629), (nb078_alpha_dummy_632 g)), ((nb078_alpha_dummy_628),
        (nb078_alpha_dummy_631 g)), ((nb078_alpha_dummy_627), (nb078_alpha_dummy_630 g)),
        ((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)), ((nb078_alpha_dummy_621),
        (nb078_alpha_dummy_623 g)), ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
        ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613),
        (nb078_alpha_dummy_615 g)), ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
        ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_621))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_623
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639) from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_639)
        from (by
          unfold
            nb078_alpha_dummy_639;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0652)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_640 g) from (by
          unfold
            nb078_alpha_dummy_640;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0653
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_628) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0650)
                  0)))) (show (nb078_alpha_dummy_631 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0651
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_621))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_623 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠
        (nb078_alpha_dummy_641) from (by
          unfold
            nb078_alpha_dummy_641;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0656)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_642 g) from (by
          unfold
            nb078_alpha_dummy_642;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0657
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_629) ≠ (nb078_alpha_dummy_637)
        from (by
          unfold
            nb078_alpha_dummy_637;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0654)
                  0)))) (show (nb078_alpha_dummy_632 g) ≠ (nb078_alpha_dummy_638 g) from (by
          unfold
            nb078_alpha_dummy_638;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0655
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                        (by
                                          unfold nb078_alpha_dummy_625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_626 g) from (by
                                          unfold nb078_alpha_dummy_626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                      ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                      ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                      ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                      ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                      ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
                                      ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from (by
                                        unfold nb078_alpha_dummy_625;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0638)
                                                0)))) (show (nb078_alpha_dummy_623 g) ≠
                                        (nb078_alpha_dummy_626 g) from (by
                                        unfold nb078_alpha_dummy_626;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0639 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_621) ≠ (nb078_alpha_dummy_625) from
                                        (by
                                          unfold nb078_alpha_dummy_625;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0638)
                                                  0)))) (show (nb078_alpha_dummy_623 g) ≠
        (nb078_alpha_dummy_626 g) from (by
                                          unfold nb078_alpha_dummy_626;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0639 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_625), (nb078_alpha_dummy_626 g)),
                                      ((nb078_alpha_dummy_621), (nb078_alpha_dummy_623 g)),
                                      ((nb078_alpha_dummy_622), (nb078_alpha_dummy_624 g)),
                                      ((nb078_alpha_dummy_614), (nb078_alpha_dummy_616 g)),
                                      ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
                                      ((nb078_alpha_dummy_619), (nb078_alpha_dummy_620 g)),
                                      ((nb078_alpha_dummy_617), (nb078_alpha_dummy_618 g)),
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
