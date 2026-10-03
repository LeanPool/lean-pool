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

@[expose]
noncomputable def nb078_split_alpha_0050 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
        ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
        ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
        ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_477))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_477)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_478 g))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_478 g))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_453) from (by
                                unfold nb078_alpha_dummy_453;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                            (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_455 g) from (by
                                unfold nb078_alpha_dummy_455;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_454) from (by
                                  unfold nb078_alpha_dummy_454;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                              (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_456 g) from
                                (by
                                  unfold nb078_alpha_dummy_456;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_479) from (by
                                    unfold nb078_alpha_dummy_479;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0498) 0)))) (show
                                  (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_480 g) from (by
                                    unfold nb078_alpha_dummy_480;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0499 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_477) from
                                    (by
                                      unfold nb078_alpha_dummy_477;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0496)
                                              0)))) (show
                                    (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_478 g) from
                                    (by
                                      unfold nb078_alpha_dummy_478;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0497 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_448 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_460) from (by
          unfold nb078_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_463 g) from (by
          unfold nb078_alpha_dummy_463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_459) from (by
          unfold nb078_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_462 g) from (by
          unfold nb078_alpha_dummy_462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457)
        from (by
          unfold nb078_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470)
                  0)))) (show (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from (by
          unfold nb078_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460),
        (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)),
        ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453),
        (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
        ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477),
        (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
        ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475),
        (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_467) from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_467)
        from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_467) from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_467)
        from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460),
        (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)),
        ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453),
        (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
        ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477),
        (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
        ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475),
        (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠
        (nb078_alpha_dummy_471) from (by
          unfold
            nb078_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_472 g) from (by
          unfold
            nb078_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_471)
        from (by
          unfold
            nb078_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_472 g) from (by
          unfold
            nb078_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_473) from (by
          unfold
            nb078_alpha_dummy_473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_474 g) from (by
          unfold
            nb078_alpha_dummy_474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠
        (nb078_alpha_dummy_473) from (by
          unfold
            nb078_alpha_dummy_473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_474 g) from (by
          unfold
            nb078_alpha_dummy_474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                        (by
                                          unfold nb078_alpha_dummy_457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
                                          unfold nb078_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                      ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                      ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                      ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)),
                                      ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
                                        unfold nb078_alpha_dummy_457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078_alpha_dummy_455 g) ≠
                                        (nb078_alpha_dummy_458 g) from (by
                                        unfold nb078_alpha_dummy_458;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0471 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                        (by
                                          unfold nb078_alpha_dummy_457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
                                          unfold nb078_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                      ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                      ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                      ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)),
                                      ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_453) from (by
                                unfold nb078_alpha_dummy_453;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0468) 0))))
                            (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_455 g) from (by
                                unfold nb078_alpha_dummy_455;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0469 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_454) from (by
                                  unfold nb078_alpha_dummy_454;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0468) 1))))
                              (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_456 g) from
                                (by
                                  unfold nb078_alpha_dummy_456;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0469 g) 1))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_479) from (by
                                    unfold nb078_alpha_dummy_479;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0498) 0)))) (show
                                  (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_480 g) from (by
                                    unfold nb078_alpha_dummy_480;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0499 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_477) from
                                    (by
                                      unfold nb078_alpha_dummy_477;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0496)
                                              0)))) (show
                                    (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_478 g) from
                                    (by
                                      unfold nb078_alpha_dummy_478;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0497 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_448 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_460) from (by
          unfold nb078_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 1)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_463 g) from (by
          unfold nb078_alpha_dummy_463;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_459) from (by
          unfold nb078_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0472) 0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_462 g) from (by
          unfold nb078_alpha_dummy_462;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0473 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457)
        from (by
          unfold nb078_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470)
                  0)))) (show (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from (by
          unfold nb078_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460),
        (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)),
        ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453),
        (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
        ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477),
        (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
        ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475),
        (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_467) from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_467)
        from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_467) from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0476)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0477
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0474)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0475
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_467)
        from (by
          unfold
            nb078_alpha_dummy_467;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0480)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_468 g) from (by
          unfold
            nb078_alpha_dummy_468;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0481
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_465)
        from (by
          unfold
            nb078_alpha_dummy_465;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0478)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_466 g) from (by
          unfold
            nb078_alpha_dummy_466;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0479
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460),
        (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)),
        ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453),
        (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
        ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)), ((nb078_alpha_dummy_477),
        (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
        ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_475),
        (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠
        (nb078_alpha_dummy_471) from (by
          unfold
            nb078_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_472 g) from (by
          unfold
            nb078_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_471)
        from (by
          unfold
            nb078_alpha_dummy_471;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0484)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_472 g) from (by
          unfold
            nb078_alpha_dummy_472;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0485
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0482)
                  0)))) (show (nb078_alpha_dummy_463 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0483
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_473) from (by
          unfold
            nb078_alpha_dummy_473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_474 g) from (by
          unfold
            nb078_alpha_dummy_474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠
        (nb078_alpha_dummy_473) from (by
          unfold
            nb078_alpha_dummy_473;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0488)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_474 g) from (by
          unfold
            nb078_alpha_dummy_474;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0489
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_461) ≠ (nb078_alpha_dummy_469)
        from (by
          unfold
            nb078_alpha_dummy_469;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0486)
                  0)))) (show (nb078_alpha_dummy_464 g) ≠ (nb078_alpha_dummy_470 g) from (by
          unfold
            nb078_alpha_dummy_470;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0487
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                        (by
                                          unfold nb078_alpha_dummy_457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
                                          unfold nb078_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                      ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                      ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                      ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)),
                                      ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
                                        unfold nb078_alpha_dummy_457;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0470)
                                                0)))) (show (nb078_alpha_dummy_455 g) ≠
                                        (nb078_alpha_dummy_458 g) from (by
                                        unfold nb078_alpha_dummy_458;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0471 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                        (by
                                          unfold nb078_alpha_dummy_457;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0470)
                                                  0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
                                          unfold nb078_alpha_dummy_458;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0471 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                      ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                      ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                      ((nb078_alpha_dummy_479), (nb078_alpha_dummy_480 g)),
                                      ((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)),
            ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
            ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
            ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)),
            ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
            ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
            ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
            ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
            ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0051 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
        ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)),
        ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_486))
          (Class.cv (nb078_alpha_dummy_481))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_488 g))
          (Class.cv (nb078_alpha_dummy_483 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_486) from (by
              unfold nb078_alpha_dummy_486;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 1))))
          (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_488 g) from (by
              unfold nb078_alpha_dummy_488;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_485) from (by
                unfold nb078_alpha_dummy_485;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0528) 0))))
            (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_487 g) from (by
                unfold nb078_alpha_dummy_487;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0530 g) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_515) from (by
                  unfold nb078_alpha_dummy_515;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0532) 0))))
              (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_516 g) from (by
                  unfold nb078_alpha_dummy_516;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0533 g) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_481) ≠ (nb078_alpha_dummy_489) from (by
                    unfold nb078_alpha_dummy_489;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0529) 0))))
                (show (nb078_alpha_dummy_483 g) ≠ (nb078_alpha_dummy_490 g) from (by
                    unfold nb078_alpha_dummy_490;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0531 g) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_cvv)).fv)
                    (by decide))
                  (freshVar_injective (((syn_ccnv (Class.cv g))).fv ∪ ((syn_cvv)).fv)
                    (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_482))).fv ∪
                ((Class.cv (nb078_alpha_dummy_481))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
                ((Class.cv (nb078_alpha_dummy_483 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_493) from (by
                                        unfold nb078_alpha_dummy_493;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                0)))) (show (nb078_alpha_dummy_488 g) ≠
                                        (nb078_alpha_dummy_495 g) from (by
                                        unfold nb078_alpha_dummy_495;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_494) from
                                        (by
                                          unfold nb078_alpha_dummy_494;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0506)
                                                  1)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_496 g) from (by
                                          unfold nb078_alpha_dummy_496;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0507 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_486) ≠
        (nb078_alpha_dummy_519) from (by
          unfold nb078_alpha_dummy_519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0536) 0)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_520 g) from (by
          unfold nb078_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0537 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_517) from (by
          unfold nb078_alpha_dummy_517;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0534) 0)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_518 g) from (by
          unfold nb078_alpha_dummy_518;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0535 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_486))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_488 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_500) from (by
          unfold nb078_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_503 g) from (by
          unfold nb078_alpha_dummy_503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_499)
        from (by
          unfold nb078_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_502 g) from (by
          unfold nb078_alpha_dummy_502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold
            nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_498 g) from (by
          unfold
            nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517),
        (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
        ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515),
        (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517),
        (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
        ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515),
        (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠
        (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)),
        ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494),
        (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)),
        ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)),
        ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494),
        (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)),
        ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_493) from (by
                                        unfold nb078_alpha_dummy_493;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                0)))) (show (nb078_alpha_dummy_488 g) ≠
                                        (nb078_alpha_dummy_495 g) from (by
                                        unfold nb078_alpha_dummy_495;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_494) from
                                        (by
                                          unfold nb078_alpha_dummy_494;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0506)
                                                  1)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_496 g) from (by
                                          unfold nb078_alpha_dummy_496;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0507 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_486) ≠
        (nb078_alpha_dummy_519) from (by
          unfold nb078_alpha_dummy_519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0536) 0)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_520 g) from (by
          unfold nb078_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0537 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_517) from (by
          unfold nb078_alpha_dummy_517;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0534) 0)))) (show (nb078_alpha_dummy_488 g) ≠
        (nb078_alpha_dummy_518 g) from (by
          unfold nb078_alpha_dummy_518;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0535 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_486))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_488 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_500) from (by
          unfold nb078_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_503 g) from (by
          unfold nb078_alpha_dummy_503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_499)
        from (by
          unfold nb078_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_502 g) from (by
          unfold nb078_alpha_dummy_502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold
            nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_498 g) from (by
          unfold
            nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517),
        (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
        ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515),
        (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)), ((nb078_alpha_dummy_517),
        (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
        ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_515),
        (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠
        (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)),
        ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494),
        (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)),
        ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)),
        ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494),
        (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_519), (nb078_alpha_dummy_520 g)),
        ((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_517), (nb078_alpha_dummy_518 g)),
                    ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)),
                    ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
                    ((nb078_alpha_dummy_515), (nb078_alpha_dummy_516 g)),
                    ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
                    ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
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

@[expose]
noncomputable def nb078_split_alpha_0052 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_489)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_485)
              (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_482))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_486)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_489)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_485)
                (syn_wrex (nb078_alpha_dummy_486) (Class.cv (nb078_alpha_dummy_481))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_485))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_486)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_490 g)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_487 g)
              (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_484 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_490 g)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_487 g)
                (syn_wrex (nb078_alpha_dummy_488 g) (Class.cv (nb078_alpha_dummy_483 g))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_487 g))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_488 g)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_486) from (by
                              unfold nb078_alpha_dummy_486;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0500) 1))))
                          (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_488 g) from (by
                              unfold nb078_alpha_dummy_488;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_485) from (by
                                unfold nb078_alpha_dummy_485;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0500) 0))))
                            (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_487 g) from (by
                                unfold nb078_alpha_dummy_487;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_491) from (by
                                  unfold nb078_alpha_dummy_491;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0504) 0))))
                              (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_492 g) from
                                (by
                                  unfold nb078_alpha_dummy_492;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0505 g) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_489) from (by
                                    unfold nb078_alpha_dummy_489;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0501) 0)))) (show
                                  (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_490 g) from (by
                                    unfold nb078_alpha_dummy_490;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0503 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_482))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_481))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_483 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_493) from
                                    (by
                                      unfold nb078_alpha_dummy_493;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0506)
                                              0)))) (show
                                    (nb078_alpha_dummy_488 g) ≠ (nb078_alpha_dummy_495 g) from
                                    (by
                                      unfold nb078_alpha_dummy_495;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0507 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_494) from (by
                                        unfold nb078_alpha_dummy_494;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                1)))) (show (nb078_alpha_dummy_488 g) ≠
                                        (nb078_alpha_dummy_496 g) from (by
                                        unfold nb078_alpha_dummy_496;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_486))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_488 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_500) from (by
          unfold nb078_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_503 g) from (by
          unfold nb078_alpha_dummy_503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_499)
        from (by
          unfold nb078_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_502 g) from (by
          unfold nb078_alpha_dummy_502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485),
        (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)),
        ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482),
        (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485),
        (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)),
        ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482),
        (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠
        (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497),
        (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)),
        ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠
        (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497),
        (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)),
        ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_486) from (by
                              unfold nb078_alpha_dummy_486;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0500) 1))))
                          (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_488 g) from (by
                              unfold nb078_alpha_dummy_488;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0502 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_485) from (by
                                unfold nb078_alpha_dummy_485;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0500) 0))))
                            (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_487 g) from (by
                                unfold nb078_alpha_dummy_487;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0502 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_491) from (by
                                  unfold nb078_alpha_dummy_491;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0504) 0))))
                              (show (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_492 g) from
                                (by
                                  unfold nb078_alpha_dummy_492;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0505 g) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_482) ≠ (nb078_alpha_dummy_489) from (by
                                    unfold nb078_alpha_dummy_489;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0501) 0)))) (show
                                  (nb078_alpha_dummy_484 g) ≠ (nb078_alpha_dummy_490 g) from (by
                                    unfold nb078_alpha_dummy_490;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0503 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_482))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_481))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_484 g))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_483 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_493) from
                                    (by
                                      unfold nb078_alpha_dummy_493;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0506)
                                              0)))) (show
                                    (nb078_alpha_dummy_488 g) ≠ (nb078_alpha_dummy_495 g) from
                                    (by
                                      unfold nb078_alpha_dummy_495;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0507 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_486) ≠ (nb078_alpha_dummy_494) from (by
                                        unfold nb078_alpha_dummy_494;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0506)
                                                1)))) (show (nb078_alpha_dummy_488 g) ≠
                                        (nb078_alpha_dummy_496 g) from (by
                                        unfold nb078_alpha_dummy_496;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0507 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_486))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_488 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_500) from (by
          unfold nb078_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  1)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_503 g) from (by
          unfold nb078_alpha_dummy_503;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_499)
        from (by
          unfold nb078_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0510)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_502 g) from (by
          unfold nb078_alpha_dummy_502;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0511
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497)
        from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508)
                  0)))) (show (nb078_alpha_dummy_495 g) ≠ (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485),
        (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)),
        ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482),
        (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0514)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0515
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0512)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0513
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_507) from (by
          unfold
            nb078_alpha_dummy_507;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0518)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_508 g) from (by
          unfold
            nb078_alpha_dummy_508;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0519
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_505)
        from (by
          unfold
            nb078_alpha_dummy_505;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0516)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_506 g) from (by
          unfold
            nb078_alpha_dummy_506;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0517
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_501), (nb078_alpha_dummy_504 g)), ((nb078_alpha_dummy_500),
        (nb078_alpha_dummy_503 g)), ((nb078_alpha_dummy_499), (nb078_alpha_dummy_502 g)),
        ((nb078_alpha_dummy_497), (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493),
        (nb078_alpha_dummy_495 g)), ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)),
        ((nb078_alpha_dummy_486), (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485),
        (nb078_alpha_dummy_487 g)), ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)),
        ((nb078_alpha_dummy_489), (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482),
        (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_493))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠
        (nb078_alpha_dummy_511) from (by
          unfold
            nb078_alpha_dummy_511;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0522)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_512 g) from (by
          unfold
            nb078_alpha_dummy_512;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0523
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_500) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0520)
                  0)))) (show (nb078_alpha_dummy_503 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0521
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_493))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_495 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠
        (nb078_alpha_dummy_513) from (by
          unfold
            nb078_alpha_dummy_513;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0526)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_514 g) from (by
          unfold
            nb078_alpha_dummy_514;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0527
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_501) ≠ (nb078_alpha_dummy_509)
        from (by
          unfold
            nb078_alpha_dummy_509;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0524)
                  0)))) (show (nb078_alpha_dummy_504 g) ≠ (nb078_alpha_dummy_510 g) from (by
          unfold
            nb078_alpha_dummy_510;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0525
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497),
        (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)),
        ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_493) ≠
        (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_493) ≠ (nb078_alpha_dummy_497) from (by
          unfold nb078_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0508) 0)))) (show (nb078_alpha_dummy_495 g) ≠
        (nb078_alpha_dummy_498 g) from (by
          unfold nb078_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0509 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_497),
        (nb078_alpha_dummy_498 g)), ((nb078_alpha_dummy_493), (nb078_alpha_dummy_495 g)),
        ((nb078_alpha_dummy_494), (nb078_alpha_dummy_496 g)), ((nb078_alpha_dummy_486),
        (nb078_alpha_dummy_488 g)), ((nb078_alpha_dummy_485), (nb078_alpha_dummy_487 g)),
        ((nb078_alpha_dummy_491), (nb078_alpha_dummy_492 g)), ((nb078_alpha_dummy_489),
        (nb078_alpha_dummy_490 g)), ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0051 x y g)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0051 x y g)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
