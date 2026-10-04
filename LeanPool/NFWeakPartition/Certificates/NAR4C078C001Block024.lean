/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block023

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part079`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0050`. -/
@[expose]
noncomputable def nb078SplitAlpha0050 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
        ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
        ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
        ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
        ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
        ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy477))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy446)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy477)) (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb078AlphaDummy478 g))
            (synCcompl (synCphi (Class.cv (nb078AlphaDummy448 g)))))
          (Wff.classMem (Class.cv (nb078AlphaDummy478 g))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy453) from (by
                                unfold nb078AlphaDummy453;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                            (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy455 g) from (by
                                unfold nb078AlphaDummy455;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy454) from (by
                                  unfold nb078AlphaDummy454;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                              (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy456 g) from
                                (by
                                  unfold nb078AlphaDummy456;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy479) from (by
                                    unfold nb078AlphaDummy479;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0498) 0)))) (show
                                  (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy480 g) from (by
                                    unfold nb078AlphaDummy480;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0499 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy477) from
                                    (by
                                      unfold nb078AlphaDummy477;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0496)
                                              0)))) (show
                                    (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy478 g) from
                                    (by
                                      unfold nb078AlphaDummy478;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0497 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy448 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy460) from (by
          unfold nb078AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy463 g) from (by
          unfold nb078AlphaDummy463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy459) from (by
          unfold nb078AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy462 g) from (by
          unfold nb078AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457)
        from (by
          unfold nb078AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470)
                  0)))) (show (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from (by
          unfold nb078AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy455
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠
        (nb078AlphaDummy471) from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471)
        from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠
        (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                      ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                        unfold nb078AlphaDummy457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078AlphaDummy455 g) ≠
                                        (nb078AlphaDummy458 g) from (by
                                        unfold nb078AlphaDummy458;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0471 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                      ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy453) from (by
                                unfold nb078AlphaDummy453;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                            (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy455 g) from (by
                                unfold nb078AlphaDummy455;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy454) from (by
                                  unfold nb078AlphaDummy454;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                              (show (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy456 g) from
                                (by
                                  unfold nb078AlphaDummy456;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy479) from (by
                                    unfold nb078AlphaDummy479;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0498) 0)))) (show
                                  (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy480 g) from (by
                                    unfold nb078AlphaDummy480;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0499 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078AlphaDummy446) ≠ (nb078AlphaDummy477) from
                                    (by
                                      unfold nb078AlphaDummy477;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0496)
                                              0)))) (show
                                    (nb078AlphaDummy448 g) ≠ (nb078AlphaDummy478 g) from
                                    (by
                                      unfold nb078AlphaDummy478;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0497 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078AlphaDummy446))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078AlphaDummy448 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy460) from (by
          unfold nb078AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy463 g) from (by
          unfold nb078AlphaDummy463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078AlphaDummy453) ≠ (nb078AlphaDummy459) from (by
          unfold nb078AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy462 g) from (by
          unfold nb078AlphaDummy462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy453) ≠ (nb078AlphaDummy457)
        from (by
          unfold nb078AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470)
                  0)))) (show (nb078AlphaDummy455 g) ≠ (nb078AlphaDummy458 g) from (by
          unfold nb078AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy467) from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy467)
        from (by
          unfold
            nb078AlphaDummy467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy468 g) from (by
          unfold
            nb078AlphaDummy468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy465)
        from (by
          unfold
            nb078AlphaDummy465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy466 g) from (by
          unfold
            nb078AlphaDummy466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy461), (nb078AlphaDummy464 g)), ((nb078AlphaDummy460),
        (nb078AlphaDummy463 g)), ((nb078AlphaDummy459), (nb078AlphaDummy462 g)),
        ((nb078AlphaDummy457), (nb078AlphaDummy458 g)), ((nb078AlphaDummy453),
        (nb078AlphaDummy455 g)), ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
        ((nb078AlphaDummy479), (nb078AlphaDummy480 g)), ((nb078AlphaDummy477),
        (nb078AlphaDummy478 g)), ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
        ((nb078AlphaDummy445), (nb078AlphaDummy447 g)), ((nb078AlphaDummy475),
        (nb078AlphaDummy476 g)), ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
        ((nb078AlphaDummy289), (nb078AlphaDummy292 g)), ((nb078AlphaDummy288),
        (nb078AlphaDummy291 g)), ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
        ((nb078AlphaDummy293), (nb078AlphaDummy294 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy453))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy455
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠
        (nb078AlphaDummy471) from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy471)
        from (by
          unfold
            nb078AlphaDummy471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy472 g) from (by
          unfold
            nb078AlphaDummy472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy460) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078AlphaDummy463 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy453))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy455 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy461) ≠
        (nb078AlphaDummy473) from (by
          unfold
            nb078AlphaDummy473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy474 g) from (by
          unfold
            nb078AlphaDummy474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy461) ≠ (nb078AlphaDummy469)
        from (by
          unfold
            nb078AlphaDummy469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078AlphaDummy464 g) ≠ (nb078AlphaDummy470 g) from (by
          unfold
            nb078AlphaDummy470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                      ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from (by
                                        unfold nb078AlphaDummy457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078AlphaDummy455 g) ≠
                                        (nb078AlphaDummy458 g) from (by
                                        unfold nb078AlphaDummy458;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0471 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078AlphaDummy453) ≠ (nb078AlphaDummy457) from
                                        (by
                                          unfold nb078AlphaDummy457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078AlphaDummy455 g) ≠
        (nb078AlphaDummy458 g) from (by
                                          unfold nb078AlphaDummy458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb078AlphaDummy457), (nb078AlphaDummy458 g)),
                                      ((nb078AlphaDummy453), (nb078AlphaDummy455 g)),
                                      ((nb078AlphaDummy454), (nb078AlphaDummy456 g)),
                                      ((nb078AlphaDummy479), (nb078AlphaDummy480 g)),
                                      ((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
                                      ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
                                      ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
                                      ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
                                      ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
                                      ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
                                      ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
                                      ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
                                      ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
                                      ((nb078AlphaDummy001), g),
                                      ((nb078AlphaDummy004), y),
                                      ((nb078AlphaDummy003), x)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb078AlphaDummy477), (nb078AlphaDummy478 g)),
            ((nb078AlphaDummy446), (nb078AlphaDummy448 g)),
            ((nb078AlphaDummy445), (nb078AlphaDummy447 g)),
            ((nb078AlphaDummy475), (nb078AlphaDummy476 g)),
            ((nb078AlphaDummy449), (nb078AlphaDummy450 g)),
            ((nb078AlphaDummy289), (nb078AlphaDummy292 g)),
            ((nb078AlphaDummy288), (nb078AlphaDummy291 g)),
            ((nb078AlphaDummy287), (nb078AlphaDummy290 g)),
            ((nb078AlphaDummy293), (nb078AlphaDummy294 g)),
            ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
            ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part080`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0051`. -/
@[expose]
noncomputable def nb078SplitAlpha0051 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
        ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy515), (nb078AlphaDummy516 g)),
        ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy486))
          (Class.cv (nb078AlphaDummy481))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy485))
            (synCun (synCphi (Class.cv (nb078AlphaDummy486))) (synCsn (synC0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy488 g))
          (Class.cv (nb078AlphaDummy483 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
            (synCun (synCphi (Class.cv (nb078AlphaDummy488 g))) (synCsn (synC0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy486) from (by
              unfold nb078AlphaDummy486;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
          (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy488 g) from (by
              unfold nb078AlphaDummy488;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
          (TAlphaVar.there (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy485) from (by
                unfold nb078AlphaDummy485;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
            (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy487 g) from (by
                unfold nb078AlphaDummy487;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
            (TAlphaVar.there (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy515) from (by
                  unfold nb078AlphaDummy515;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0532) 0))))
              (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy516 g) from (by
                  unfold nb078AlphaDummy516;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0533 g) 0))))
              (TAlphaVar.there (show (nb078AlphaDummy481) ≠ (nb078AlphaDummy489) from (by
                    unfold nb078AlphaDummy489;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0529) 0))))
                (show (nb078AlphaDummy483 g) ≠ (nb078AlphaDummy490 g) from (by
                    unfold nb078AlphaDummy490;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0531 g) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((synCcnv (Class.cv (nb078AlphaDummy001)))).fv ∪ ((synCvv)).fv)
                    (by decide))
                  (freshVar_injective (((synCcnv (Class.cv g))).fv ∪ ((synCvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078AlphaDummy482))).fv ∪
                ((Class.cv (nb078AlphaDummy481))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078AlphaDummy484 g))).fv ∪
                ((Class.cv (nb078AlphaDummy483 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy486) ≠ (nb078AlphaDummy493) from (by
                                        unfold nb078AlphaDummy493;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                0)))) (show (nb078AlphaDummy488 g) ≠
                                        (nb078AlphaDummy495 g) from (by
                                        unfold nb078AlphaDummy495;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy486) ≠ (nb078AlphaDummy494) from
                                        (by
                                          unfold nb078AlphaDummy494;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0506)
                                                  1)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy496 g) from (by
                                          unfold nb078AlphaDummy496;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0507 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy486) ≠
        (nb078AlphaDummy519) from (by
          unfold nb078AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0536) 0)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy520 g) from (by
          unfold nb078AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0537 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy486) ≠ (nb078AlphaDummy517) from (by
          unfold nb078AlphaDummy517;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0534) 0)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy518 g) from (by
          unfold nb078AlphaDummy518;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0535 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy486))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy488 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy500) from (by
          unfold nb078AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy503 g) from (by
          unfold nb078AlphaDummy503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy499)
        from (by
          unfold nb078AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy502 g) from (by
          unfold nb078AlphaDummy502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold
            nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy498 g) from (by
          unfold
            nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy519), (nb078AlphaDummy520 g)), ((nb078AlphaDummy517),
        (nb078AlphaDummy518 g)), ((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
        ((nb078AlphaDummy485), (nb078AlphaDummy487 g)), ((nb078AlphaDummy515),
        (nb078AlphaDummy516 g)), ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy519), (nb078AlphaDummy520 g)), ((nb078AlphaDummy517),
        (nb078AlphaDummy518 g)), ((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
        ((nb078AlphaDummy485), (nb078AlphaDummy487 g)), ((nb078AlphaDummy515),
        (nb078AlphaDummy516 g)), ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy500) ≠
        (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497), (nb078AlphaDummy498 g)),
        ((nb078AlphaDummy493), (nb078AlphaDummy495 g)), ((nb078AlphaDummy494),
        (nb078AlphaDummy496 g)), ((nb078AlphaDummy519), (nb078AlphaDummy520 g)),
        ((nb078AlphaDummy517), (nb078AlphaDummy518 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy515), (nb078AlphaDummy516 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497), (nb078AlphaDummy498 g)),
        ((nb078AlphaDummy493), (nb078AlphaDummy495 g)), ((nb078AlphaDummy494),
        (nb078AlphaDummy496 g)), ((nb078AlphaDummy519), (nb078AlphaDummy520 g)),
        ((nb078AlphaDummy517), (nb078AlphaDummy518 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy515), (nb078AlphaDummy516 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078AlphaDummy486) ≠ (nb078AlphaDummy493) from (by
                                        unfold nb078AlphaDummy493;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                0)))) (show (nb078AlphaDummy488 g) ≠
                                        (nb078AlphaDummy495 g) from (by
                                        unfold nb078AlphaDummy495;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078AlphaDummy486) ≠ (nb078AlphaDummy494) from
                                        (by
                                          unfold nb078AlphaDummy494;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0506)
                                                  1)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy496 g) from (by
                                          unfold nb078AlphaDummy496;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0507 g) 1))))
                                      (TAlphaVar.there (show (nb078AlphaDummy486) ≠
        (nb078AlphaDummy519) from (by
          unfold nb078AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0536) 0)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy520 g) from (by
          unfold nb078AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0537 g) 0)))) (TAlphaVar.there (show
        (nb078AlphaDummy486) ≠ (nb078AlphaDummy517) from (by
          unfold nb078AlphaDummy517;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0534) 0)))) (show (nb078AlphaDummy488 g) ≠
        (nb078AlphaDummy518 g) from (by
          unfold nb078AlphaDummy518;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0535 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy486))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078AlphaDummy488 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy500) from (by
          unfold nb078AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy503 g) from (by
          unfold nb078AlphaDummy503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy499)
        from (by
          unfold nb078AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy502 g) from (by
          unfold nb078AlphaDummy502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold
            nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy498 g) from (by
          unfold
            nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy519), (nb078AlphaDummy520 g)), ((nb078AlphaDummy517),
        (nb078AlphaDummy518 g)), ((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
        ((nb078AlphaDummy485), (nb078AlphaDummy487 g)), ((nb078AlphaDummy515),
        (nb078AlphaDummy516 g)), ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy519), (nb078AlphaDummy520 g)), ((nb078AlphaDummy517),
        (nb078AlphaDummy518 g)), ((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
        ((nb078AlphaDummy485), (nb078AlphaDummy487 g)), ((nb078AlphaDummy515),
        (nb078AlphaDummy516 g)), ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)), ((nb078AlphaDummy481),
        (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy500) ≠
        (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497), (nb078AlphaDummy498 g)),
        ((nb078AlphaDummy493), (nb078AlphaDummy495 g)), ((nb078AlphaDummy494),
        (nb078AlphaDummy496 g)), ((nb078AlphaDummy519), (nb078AlphaDummy520 g)),
        ((nb078AlphaDummy517), (nb078AlphaDummy518 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy515), (nb078AlphaDummy516 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497), (nb078AlphaDummy498 g)),
        ((nb078AlphaDummy493), (nb078AlphaDummy495 g)), ((nb078AlphaDummy494),
        (nb078AlphaDummy496 g)), ((nb078AlphaDummy519), (nb078AlphaDummy520 g)),
        ((nb078AlphaDummy517), (nb078AlphaDummy518 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy515), (nb078AlphaDummy516 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb078AlphaDummy517), (nb078AlphaDummy518 g)),
                    ((nb078AlphaDummy486), (nb078AlphaDummy488 g)),
                    ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
                    ((nb078AlphaDummy515), (nb078AlphaDummy516 g)),
                    ((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
                    ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
                    ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
                    ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
                    ((nb078AlphaDummy003), x)] (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part081`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb078_split_alpha_0052`. -/
@[expose]
noncomputable def nb078SplitAlpha0052 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078AlphaDummy489), (nb078AlphaDummy490 g)),
        ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy489)) (synCcompl
            (Class.cab (nb078AlphaDummy485)
              (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy482))
                (Wff.classEq (Class.cv (nb078AlphaDummy485))
                  (synCphi (Class.cv (nb078AlphaDummy486)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy489)) (synCcompl
              (Class.cab (nb078AlphaDummy485)
                (synWrex (nb078AlphaDummy486) (Class.cv (nb078AlphaDummy481))
                  (Wff.classEq (Class.cv (nb078AlphaDummy485))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy486)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078AlphaDummy490 g)) (synCcompl
            (Class.cab (nb078AlphaDummy487 g)
              (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy484 g))
                (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                  (synCphi (Class.cv (nb078AlphaDummy488 g)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078AlphaDummy490 g)) (synCcompl
              (Class.cab (nb078AlphaDummy487 g)
                (synWrex (nb078AlphaDummy488 g) (Class.cv (nb078AlphaDummy483 g))
                  (Wff.classEq (Class.cv (nb078AlphaDummy487 g))
                    (synCun (synCphi (Class.cv (nb078AlphaDummy488 g)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy486) from (by
                              unfold nb078AlphaDummy486;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0500) 1))))
                          (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy488 g) from (by
                              unfold nb078AlphaDummy488;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy485) from (by
                                unfold nb078AlphaDummy485;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0500) 0))))
                            (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy487 g) from (by
                                unfold nb078AlphaDummy487;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy491) from (by
                                  unfold nb078AlphaDummy491;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0504) 0))))
                              (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy492 g) from
                                (by
                                  unfold nb078AlphaDummy492;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0505 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy489) from (by
                                    unfold nb078AlphaDummy489;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0501) 0)))) (show
                                  (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy490 g) from (by
                                    unfold nb078AlphaDummy490;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0503 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy482))).fv ∪
                              ((Class.cv (nb078AlphaDummy481))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy484 g))).fv ∪
                              ((Class.cv (nb078AlphaDummy483 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy486) ≠ (nb078AlphaDummy493) from
                                    (by
                                      unfold nb078AlphaDummy493;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0506)
                                              0)))) (show
                                    (nb078AlphaDummy488 g) ≠ (nb078AlphaDummy495 g) from
                                    (by
                                      unfold nb078AlphaDummy495;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0507 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy486) ≠ (nb078AlphaDummy494) from (by
                                        unfold nb078AlphaDummy494;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                1)))) (show (nb078AlphaDummy488 g) ≠
                                        (nb078AlphaDummy496 g) from (by
                                        unfold nb078AlphaDummy496;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy486))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy488 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy500) from (by
          unfold nb078AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy503 g) from (by
          unfold nb078AlphaDummy503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy499)
        from (by
          unfold nb078AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy502 g) from (by
          unfold nb078AlphaDummy502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy486), (nb078AlphaDummy488 g)), ((nb078AlphaDummy485),
        (nb078AlphaDummy487 g)), ((nb078AlphaDummy491), (nb078AlphaDummy492 g)),
        ((nb078AlphaDummy489), (nb078AlphaDummy490 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy486), (nb078AlphaDummy488 g)), ((nb078AlphaDummy485),
        (nb078AlphaDummy487 g)), ((nb078AlphaDummy491), (nb078AlphaDummy492 g)),
        ((nb078AlphaDummy489), (nb078AlphaDummy490 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy500) ≠
        (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497),
        (nb078AlphaDummy498 g)), ((nb078AlphaDummy493), (nb078AlphaDummy495 g)),
        ((nb078AlphaDummy494), (nb078AlphaDummy496 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy491), (nb078AlphaDummy492 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy493) ≠
        (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497),
        (nb078AlphaDummy498 g)), ((nb078AlphaDummy493), (nb078AlphaDummy495 g)),
        ((nb078AlphaDummy494), (nb078AlphaDummy496 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy491), (nb078AlphaDummy492 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy486) from (by
                              unfold nb078AlphaDummy486;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0500) 1))))
                          (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy488 g) from (by
                              unfold nb078AlphaDummy488;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
                          (TAlphaVar.there
                            (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy485) from (by
                                unfold nb078AlphaDummy485;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0500) 0))))
                            (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy487 g) from (by
                                unfold nb078AlphaDummy487;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
                            (TAlphaVar.there
                              (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy491) from (by
                                  unfold nb078AlphaDummy491;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0504) 0))))
                              (show (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy492 g) from
                                (by
                                  unfold nb078AlphaDummy492;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0505 g) 0))))
                              (TAlphaVar.there
                                (show (nb078AlphaDummy482) ≠ (nb078AlphaDummy489) from (by
                                    unfold nb078AlphaDummy489;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0501) 0)))) (show
                                  (nb078AlphaDummy484 g) ≠ (nb078AlphaDummy490 g) from (by
                                    unfold nb078AlphaDummy490;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0503 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078AlphaDummy482))).fv ∪
                              ((Class.cv (nb078AlphaDummy481))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078AlphaDummy484 g))).fv ∪
                              ((Class.cv (nb078AlphaDummy483 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078AlphaDummy486) ≠ (nb078AlphaDummy493) from
                                    (by
                                      unfold nb078AlphaDummy493;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0506)
                                              0)))) (show
                                    (nb078AlphaDummy488 g) ≠ (nb078AlphaDummy495 g) from
                                    (by
                                      unfold nb078AlphaDummy495;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0507 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078AlphaDummy486) ≠ (nb078AlphaDummy494) from (by
                                        unfold nb078AlphaDummy494;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                1)))) (show (nb078AlphaDummy488 g) ≠
                                        (nb078AlphaDummy496 g) from (by
                                        unfold nb078AlphaDummy496;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy486))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078AlphaDummy488 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy500) from (by
          unfold nb078AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy503 g) from (by
          unfold nb078AlphaDummy503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511 g)
                  1)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy499)
        from (by
          unfold nb078AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy502 g) from (by
          unfold nb078AlphaDummy502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy493) ≠ (nb078AlphaDummy497)
        from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078AlphaDummy495 g) ≠ (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy486), (nb078AlphaDummy488 g)), ((nb078AlphaDummy485),
        (nb078AlphaDummy487 g)), ((nb078AlphaDummy491), (nb078AlphaDummy492 g)),
        ((nb078AlphaDummy489), (nb078AlphaDummy490 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy507) from (by
          unfold
            nb078AlphaDummy507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy508 g) from (by
          unfold
            nb078AlphaDummy508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy505)
        from (by
          unfold
            nb078AlphaDummy505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy506 g) from (by
          unfold
            nb078AlphaDummy506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb078AlphaDummy501), (nb078AlphaDummy504 g)), ((nb078AlphaDummy500),
        (nb078AlphaDummy503 g)), ((nb078AlphaDummy499), (nb078AlphaDummy502 g)),
        ((nb078AlphaDummy497), (nb078AlphaDummy498 g)), ((nb078AlphaDummy493),
        (nb078AlphaDummy495 g)), ((nb078AlphaDummy494), (nb078AlphaDummy496 g)),
        ((nb078AlphaDummy486), (nb078AlphaDummy488 g)), ((nb078AlphaDummy485),
        (nb078AlphaDummy487 g)), ((nb078AlphaDummy491), (nb078AlphaDummy492 g)),
        ((nb078AlphaDummy489), (nb078AlphaDummy490 g)), ((nb078AlphaDummy482),
        (nb078AlphaDummy484 g)), ((nb078AlphaDummy481), (nb078AlphaDummy483 g)),
        ((nb078AlphaDummy001), g), ((nb078AlphaDummy004), y),
        ((nb078AlphaDummy003), x)] (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078AlphaDummy495 g))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078AlphaDummy493))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495
        g))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy500) ≠
        (nb078AlphaDummy511) from (by
          unfold
            nb078AlphaDummy511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy512 g) from (by
          unfold
            nb078AlphaDummy512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy500) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078AlphaDummy503 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078AlphaDummy493))).fv ∪ ((synC1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078AlphaDummy495 g))).fv ∪
        ((synC1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078AlphaDummy501) ≠
        (nb078AlphaDummy513) from (by
          unfold
            nb078AlphaDummy513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy514 g) from (by
          unfold
            nb078AlphaDummy514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078AlphaDummy501) ≠ (nb078AlphaDummy509)
        from (by
          unfold
            nb078AlphaDummy509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078AlphaDummy504 g) ≠ (nb078AlphaDummy510 g) from (by
          unfold
            nb078AlphaDummy510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497),
        (nb078AlphaDummy498 g)), ((nb078AlphaDummy493), (nb078AlphaDummy495 g)),
        ((nb078AlphaDummy494), (nb078AlphaDummy496 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy491), (nb078AlphaDummy492 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)]
        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078AlphaDummy493) ≠
        (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078AlphaDummy493) ≠ (nb078AlphaDummy497) from (by
          unfold nb078AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078AlphaDummy495 g) ≠
        (nb078AlphaDummy498 g) from (by
          unfold nb078AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.reflOfClosed [((nb078AlphaDummy497),
        (nb078AlphaDummy498 g)), ((nb078AlphaDummy493), (nb078AlphaDummy495 g)),
        ((nb078AlphaDummy494), (nb078AlphaDummy496 g)), ((nb078AlphaDummy486),
        (nb078AlphaDummy488 g)), ((nb078AlphaDummy485), (nb078AlphaDummy487 g)),
        ((nb078AlphaDummy491), (nb078AlphaDummy492 g)), ((nb078AlphaDummy489),
        (nb078AlphaDummy490 g)), ((nb078AlphaDummy482), (nb078AlphaDummy484 g)),
        ((nb078AlphaDummy481), (nb078AlphaDummy483 g)), ((nb078AlphaDummy001), g),
        ((nb078AlphaDummy004), y), ((nb078AlphaDummy003), x)] (synCnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0051 x y g)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078SplitAlpha0051 x y g)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
