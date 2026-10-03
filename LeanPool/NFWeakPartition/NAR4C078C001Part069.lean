/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block020

/-! NF weak partition development: NAR4C078C001Part069. -/


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
noncomputable def nb078_split_alpha_0039 (x : Var) (y : Var) (g : Var) :
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
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem (Class.cv (nb078_alpha_dummy_477))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))
      (Wff.classMem (Class.cv (nb078_alpha_dummy_478 g))
        (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_456 g) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_0498) 0))))
                            (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_480 g) from (by
                                unfold nb078_alpha_dummy_480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0499 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_477) from (by
                                  unfold nb078_alpha_dummy_477;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0496) 0))))
                              (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_478 g) from
                                (by
                                  unfold nb078_alpha_dummy_478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0497 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_453) ≠
        (nb078_alpha_dummy_460) from (by
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
                  (nb078_support_mem_0473 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
          unfold nb078_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470) 0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
          unfold nb078_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_471) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                    (by
                                      unfold nb078_alpha_dummy_457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from
                                    (by
                                      unfold nb078_alpha_dummy_458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
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
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
                                    unfold nb078_alpha_dummy_457;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0470) 0)))) (show
                                  (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from (by
                                    unfold nb078_alpha_dummy_458;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0471 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                    (by
                                      unfold nb078_alpha_dummy_457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from
                                    (by
                                      unfold nb078_alpha_dummy_458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
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
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
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
                          (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_456 g) from (by
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
                                      (mem_lt_freshVar (nb078_support_mem_0498) 0))))
                            (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_480 g) from (by
                                unfold nb078_alpha_dummy_480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0499 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_446) ≠ (nb078_alpha_dummy_477) from (by
                                  unfold nb078_alpha_dummy_477;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0496) 0))))
                              (show (nb078_alpha_dummy_448 g) ≠ (nb078_alpha_dummy_478 g) from
                                (by
                                  unfold nb078_alpha_dummy_478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0497 g) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_453) ≠
        (nb078_alpha_dummy_460) from (by
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
                  (nb078_support_mem_0473 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
          unfold nb078_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0470) 0)))) (show (nb078_alpha_dummy_455 g) ≠
        (nb078_alpha_dummy_458 g) from (by
          unfold nb078_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0471 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_460) ≠ (nb078_alpha_dummy_471) from (by
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
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                    (by
                                      unfold nb078_alpha_dummy_457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from
                                    (by
                                      unfold nb078_alpha_dummy_458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
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
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from (by
                                    unfold nb078_alpha_dummy_457;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0470) 0)))) (show
                                  (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from (by
                                    unfold nb078_alpha_dummy_458;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0471 g)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_457) from
                                    (by
                                      unfold nb078_alpha_dummy_457;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0470)
                                              0)))) (show
                                    (nb078_alpha_dummy_455 g) ≠ (nb078_alpha_dummy_458 g) from
                                    (by
                                      unfold nb078_alpha_dummy_458;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0471 g)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
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
                                  ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                  ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                  ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                  ((nb078_alpha_dummy_003), x)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0040 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_293))
          (syn_cop (Class.cv (nb078_alpha_dummy_287)) (Class.cv (nb078_alpha_dummy_288))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_289) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_294 g))
          (syn_cop (Class.cv (nb078_alpha_dummy_290 g)) (Class.cv (nb078_alpha_dummy_291 g))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_293) from (by
                unfold nb078_alpha_dummy_293;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0292) 0))))) (Ne.symm
            (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_294 g) from (by
                unfold nb078_alpha_dummy_294;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0293 g) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_293) from
                (by
                  unfold nb078_alpha_dummy_293;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0290) 0)))))
            (Ne.symm (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_294 g) from (by
                  unfold nb078_alpha_dummy_294;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0291 g) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0030 x y g)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_296) from
                                    (by
                                      unfold nb078_alpha_dummy_296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0322)
                                              1)))) (show
                                    (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_298 g) from
                                    (by
                                      unfold nb078_alpha_dummy_298;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0324 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_295) from (by
                                        unfold nb078_alpha_dummy_295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0322)
                                                0)))) (show (nb078_alpha_dummy_291 g) ≠
                                        (nb078_alpha_dummy_297 g) from (by
                                        unfold nb078_alpha_dummy_297;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0324 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_325) from
                                        (by
                                          unfold nb078_alpha_dummy_325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0326)
                                                  0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_326 g) from (by
                                          unfold nb078_alpha_dummy_326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0327 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠
        (nb078_alpha_dummy_299) from (by
          unfold nb078_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0323) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_300 g) from (by
          unfold nb078_alpha_dummy_300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0325 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0031 x y g)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_296) from
                                    (by
                                      unfold nb078_alpha_dummy_296;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0322)
                                              1)))) (show
                                    (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_298 g) from
                                    (by
                                      unfold nb078_alpha_dummy_298;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0324 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_295) from (by
                                        unfold nb078_alpha_dummy_295;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0322)
                                                0)))) (show (nb078_alpha_dummy_291 g) ≠
                                        (nb078_alpha_dummy_297 g) from (by
                                        unfold nb078_alpha_dummy_297;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0324 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_325) from
                                        (by
                                          unfold nb078_alpha_dummy_325;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0326)
                                                  0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_326 g) from (by
                                          unfold nb078_alpha_dummy_326;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0327 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠
        (nb078_alpha_dummy_299) from (by
          unfold nb078_alpha_dummy_299;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0323) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_300 g) from (by
          unfold nb078_alpha_dummy_300;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0325 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0031 x y g)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0032 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠
        (nb078_alpha_dummy_332) from (by
          unfold nb078_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 1)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_334 g) from (by
          unfold nb078_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_361) from (by
          unfold nb078_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_362 g) from (by
          unfold nb078_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_335) from (by
          unfold nb078_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_336 g) from (by
          unfold nb078_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0033 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332),
        (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
        ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335),
        (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠
        (nb078_alpha_dummy_332) from (by
          unfold nb078_alpha_dummy_332;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 1)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_334 g) from (by
          unfold nb078_alpha_dummy_334;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331) from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_361) from (by
          unfold nb078_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_362 g) from (by
          unfold nb078_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_335) from (by
          unfold nb078_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361) 0)))) (show (nb078_alpha_dummy_292 g) ≠
        (nb078_alpha_dummy_336 g) from (by
          unfold nb078_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_289))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0033 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_363), (nb078_alpha_dummy_364 g)), ((nb078_alpha_dummy_332),
        (nb078_alpha_dummy_334 g)), ((nb078_alpha_dummy_331), (nb078_alpha_dummy_333 g)),
        ((nb078_alpha_dummy_361), (nb078_alpha_dummy_362 g)), ((nb078_alpha_dummy_335),
        (nb078_alpha_dummy_336 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                            (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_371) from (by
                                unfold nb078_alpha_dummy_371;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0372) 0))))) (Ne.symm
                            (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_372 g) from (by
                                unfold nb078_alpha_dummy_372;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0373 g) 0)))))
                          (TAlphaVar.there (Ne.symm
                              (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_371) from (by
                                  unfold nb078_alpha_dummy_371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0370) 0)))))
                            (Ne.symm (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_372 g)
                                from (by
                                  unfold nb078_alpha_dummy_372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0371 g) 0)))))
                            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0034 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
          unfold nb078_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
          unfold nb078_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373)
        from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_403)
        from (by
          unfold nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold nb078_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0407
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_377)
        from (by
          unfold nb078_alpha_dummy_377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_378 g) from (by
          unfold nb078_alpha_dummy_378;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0405
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪
        ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0035 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
          unfold nb078_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
          unfold nb078_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373)
        from (by
          unfold nb078_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold nb078_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_403)
        from (by
          unfold nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold nb078_alpha_dummy_404;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0407
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_377)
        from (by
          unfold nb078_alpha_dummy_377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_378 g) from (by
          unfold nb078_alpha_dummy_378;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0405
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_367))).fv ∪
        ((Class.cv (nb078_alpha_dummy_368))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_369 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_370 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0035 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0036 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
          unfold nb078_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
          unfold nb078_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409)
        from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_439)
        from (by
          unfold nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold nb078_alpha_dummy_440;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0445
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_413)
        from (by
          unfold nb078_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_414 g) from (by
          unfold nb078_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0443
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_368))).fv ∪
        ((Class.cv (nb078_alpha_dummy_367))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0037 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
          unfold nb078_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
          unfold nb078_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409)
        from (by
          unfold nb078_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold nb078_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_439)
        from (by
          unfold nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold nb078_alpha_dummy_440;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0445
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_413)
        from (by
          unfold nb078_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_414 g) from (by
          unfold nb078_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0443
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_368))).fv ∪
        ((Class.cv (nb078_alpha_dummy_367))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_370 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_369 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0037 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                          (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_368) from (by
                              unfold nb078_alpha_dummy_368;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0460) 1))))
                          (show g ≠ (nb078_alpha_dummy_370 g) from (by
                              unfold nb078_alpha_dummy_370;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0461 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_367) from (by
                                unfold nb078_alpha_dummy_367;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0460) 0))))
                            (show g ≠ (nb078_alpha_dummy_369 g) from (by
                                unfold nb078_alpha_dummy_369;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0461 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_371) from (by
                                  unfold nb078_alpha_dummy_371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0458) 0))))
                              (show g ≠ (nb078_alpha_dummy_372 g) from (by
                                  unfold nb078_alpha_dummy_372;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0459 g) 0))))
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_289) from (by
                                    unfold nb078_alpha_dummy_289;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0454) 2))))
                                (show g ≠ (nb078_alpha_dummy_292 g) from (by
                                    unfold nb078_alpha_dummy_292;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0456 g)
                                            2)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_288) from
                                    (by
                                      unfold nb078_alpha_dummy_288;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0454)
                                              1)))) (show g ≠ (nb078_alpha_dummy_291 g) from (by
                                      unfold nb078_alpha_dummy_291;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0456 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_287) from (by
                                        unfold nb078_alpha_dummy_287;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0454)
                                                0)))) (show g ≠ (nb078_alpha_dummy_290 g) from
                                      (by
                                        unfold nb078_alpha_dummy_290;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0456 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_293) from
                                        (by
                                          unfold nb078_alpha_dummy_293;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0455)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_294 g) from
                                        (by
                                          unfold nb078_alpha_dummy_294;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0457 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_285) from (by
          unfold nb078_alpha_dummy_285;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0452) 0)))) (show g ≠ (nb078_alpha_dummy_286 g) from (by
          unfold nb078_alpha_dummy_286;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0453 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_283) from (by
          unfold nb078_alpha_dummy_283;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0450) 0)))) (show g ≠ (nb078_alpha_dummy_284 g) from (by
          unfold nb078_alpha_dummy_284;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0451 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0038 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠
        (nb078_alpha_dummy_446) from (by
          unfold nb078_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 1)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_448 g) from (by
          unfold nb078_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_475) from (by
          unfold nb078_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_476 g) from (by
          unfold nb078_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_449) from (by
          unfold nb078_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_450 g) from (by
          unfold nb078_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv ∪
        ((syn_ccnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0039 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446),
        (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
        ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449),
        (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠
        (nb078_alpha_dummy_446) from (by
          unfold nb078_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 1)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_448 g) from (by
          unfold nb078_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445) from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_475) from (by
          unfold nb078_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_476 g) from (by
          unfold nb078_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_449) from (by
          unfold nb078_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491) 0)))) (show (nb078_alpha_dummy_291 g) ≠
        (nb078_alpha_dummy_450 g) from (by
          unfold nb078_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv g)).fv ∪
        ((syn_ccnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_289))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0039 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_477), (nb078_alpha_dummy_478 g)), ((nb078_alpha_dummy_446),
        (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
        ((nb078_alpha_dummy_475), (nb078_alpha_dummy_476 g)), ((nb078_alpha_dummy_449),
        (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_289) from (by
                    unfold nb078_alpha_dummy_289;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 2))))
                (show g ≠ (nb078_alpha_dummy_292 g) from (by
                    unfold nb078_alpha_dummy_292;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
                (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_288) from
                    (by
                      unfold nb078_alpha_dummy_288;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 1))))
                  (show g ≠ (nb078_alpha_dummy_291 g) from (by
                      unfold nb078_alpha_dummy_291;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0456 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_287) from
                      (by
                        unfold nb078_alpha_dummy_287;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0454) 0))))
                    (show g ≠ (nb078_alpha_dummy_290 g) from (by
                        unfold nb078_alpha_dummy_290;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0456 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_293) from (by
                          unfold nb078_alpha_dummy_293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0455) 0))))
                      (show g ≠ (nb078_alpha_dummy_294 g) from (by
                          unfold nb078_alpha_dummy_294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0457 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_285) from (by
                            unfold nb078_alpha_dummy_285;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0452) 0))))
                        (show g ≠ (nb078_alpha_dummy_286 g) from (by
                            unfold nb078_alpha_dummy_286;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0453 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_283) from (by
                              unfold nb078_alpha_dummy_283;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0450) 0))))
                          (show g ≠ (nb078_alpha_dummy_284 g) from (by
                              unfold nb078_alpha_dummy_284;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0451 g) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

theorem nb078_wpp_notmem_1216 : (nb078_alpha_dummy_285) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_285, fv_syn_cid] using (nb078_compact_fv_empty_0240)

theorem nb078_wpp_notmem_1217 (g : Var) : (nb078_alpha_dummy_286 g) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_286, fv_syn_cid] using (nb078_compact_fv_empty_0241 g)

theorem nb078_wpp_notmem_1218 : (nb078_alpha_dummy_283) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_283, fv_syn_cid] using (nb078_compact_fv_empty_0242)

theorem nb078_wpp_notmem_1219 (g : Var) : (nb078_alpha_dummy_284 g) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_284, fv_syn_cid] using (nb078_compact_fv_empty_0243 g)

theorem nb078_wpp_notmem_1220 : (nb078_alpha_dummy_001) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_001, fv_syn_cid] using (nb078_compact_fv_empty_0244)

theorem nb078_wpp_notmem_1221 (g : Var) : g ∉ ((syn_cid)).fv := by
  simpa only [fv_syn_cid] using (nb078_compact_fv_empty_0245 g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
