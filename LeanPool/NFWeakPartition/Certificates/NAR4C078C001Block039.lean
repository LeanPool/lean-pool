/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block038

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part118`. -/


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
noncomputable def nb078_split_alpha_0093 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
        ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
        ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_443))
          (syn_cphi (Class.cv (nb078_alpha_dummy_410)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_443))
            (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_444 g))
          (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_444 g))
            (syn_cphi (Class.cv (nb078_alpha_dummy_412 g)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_417) from
                    (by
                      unfold nb078_alpha_dummy_417;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                  (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_419 g) from (by
                      unfold nb078_alpha_dummy_419;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_418) from
                      (by
                        unfold nb078_alpha_dummy_418;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                    (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_420 g) from (by
                        unfold nb078_alpha_dummy_420;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0419 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_443) from (by
                          unfold nb078_alpha_dummy_443;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0448) 0))))
                      (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_444 g) from (by
                          unfold nb078_alpha_dummy_444;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0449 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_441) from (by
                            unfold nb078_alpha_dummy_441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0446) 0))))
                        (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_442 g) from (by
                            unfold nb078_alpha_dummy_442;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0447 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_424) from (by
                                        unfold nb078_alpha_dummy_424;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0422)
                                                1)))) (show (nb078_alpha_dummy_419 g) ≠
                                        (nb078_alpha_dummy_427 g) from (by
                                        unfold nb078_alpha_dummy_427;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0423 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_423) from
                                        (by
                                          unfold nb078_alpha_dummy_423;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0422)
                                                  0)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_426 g) from (by
                                          unfold nb078_alpha_dummy_426;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0423 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_417) ≠
        (nb078_alpha_dummy_421) from (by
          unfold nb078_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420) 0)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_422 g) from (by
          unfold nb078_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_425),
        (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)),
                                        ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)),
                                        ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                                        ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                                        ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                                        ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
                                        ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
                                        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                                        ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                                        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
                                        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
                                        ((nb078_alpha_dummy_001), g),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠
        (nb078_alpha_dummy_431) from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_431)
        from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_431) from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_431)
        from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)),
        ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423),
        (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
        ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418),
        (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
        ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠
        (nb078_alpha_dummy_435) from (by
          unfold
            nb078_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_436 g) from (by
          unfold
            nb078_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_435)
        from (by
          unfold
            nb078_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_436 g) from (by
          unfold
            nb078_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_437) from (by
          unfold
            nb078_alpha_dummy_437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_438 g) from (by
          unfold
            nb078_alpha_dummy_438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠
        (nb078_alpha_dummy_437) from (by
          unfold
            nb078_alpha_dummy_437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_438 g) from (by
          unfold
            nb078_alpha_dummy_438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                unfold nb078_alpha_dummy_421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from (by
                                unfold nb078_alpha_dummy_422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                            ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                            ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                            ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
                            ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
                            ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                            ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                            ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
                            ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                              unfold nb078_alpha_dummy_421;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                          (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from (by
                              unfold nb078_alpha_dummy_422;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                unfold nb078_alpha_dummy_421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from (by
                                unfold nb078_alpha_dummy_422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                            ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                            ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                            ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
                            ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
                            ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                            ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                            ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
                            ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_417) from (by
                        unfold nb078_alpha_dummy_417;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                    (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_419 g) from (by
                        unfold nb078_alpha_dummy_419;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0419 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_418) from (by
                          unfold nb078_alpha_dummy_418;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0418) 1))))
                      (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_420 g) from (by
                          unfold nb078_alpha_dummy_420;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_443) from (by
                            unfold nb078_alpha_dummy_443;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0448) 0))))
                        (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_444 g) from (by
                            unfold nb078_alpha_dummy_444;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0449 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_441) from (by
                              unfold nb078_alpha_dummy_441;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0446) 0))))
                          (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_442 g) from (by
                              unfold nb078_alpha_dummy_442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0447 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_424) from
                                        (by
                                          unfold nb078_alpha_dummy_424;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0422)
                                                  1)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_427 g) from (by
                                          unfold nb078_alpha_dummy_427;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0423 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_417) ≠
        (nb078_alpha_dummy_423) from (by
          unfold nb078_alpha_dummy_423;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 0)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_426 g) from (by
          unfold nb078_alpha_dummy_426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
          unfold nb078_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420) 0)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_422 g) from (by
          unfold nb078_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0421 g) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_425),
        (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424), (nb078_alpha_dummy_427 g)),
        ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)), ((nb078_alpha_dummy_421),
        (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
        ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)), ((nb078_alpha_dummy_443),
        (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409),
        (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650),
        (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)),
        ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠
        (nb078_alpha_dummy_431) from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_431)
        from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_431) from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0426)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0427
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0424)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0425
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_431)
        from (by
          unfold
            nb078_alpha_dummy_431;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0430)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_432 g) from (by
          unfold
            nb078_alpha_dummy_432;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0431
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_429)
        from (by
          unfold
            nb078_alpha_dummy_429;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0428)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_430 g) from (by
          unfold
            nb078_alpha_dummy_430;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0429
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_425), (nb078_alpha_dummy_428 g)), ((nb078_alpha_dummy_424),
        (nb078_alpha_dummy_427 g)), ((nb078_alpha_dummy_423), (nb078_alpha_dummy_426 g)),
        ((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)), ((nb078_alpha_dummy_417),
        (nb078_alpha_dummy_419 g)), ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
        ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)), ((nb078_alpha_dummy_441),
        (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
        ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_439),
        (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367),
        (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)), ((nb078_alpha_dummy_649),
        (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653), (nb078_alpha_dummy_654 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠
        (nb078_alpha_dummy_435) from (by
          unfold
            nb078_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_436 g) from (by
          unfold
            nb078_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_435)
        from (by
          unfold
            nb078_alpha_dummy_435;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0434)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_436 g) from (by
          unfold
            nb078_alpha_dummy_436;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0435
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0432)
                  0)))) (show (nb078_alpha_dummy_427 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0433
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_437) from (by
          unfold
            nb078_alpha_dummy_437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_438 g) from (by
          unfold
            nb078_alpha_dummy_438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠
        (nb078_alpha_dummy_437) from (by
          unfold
            nb078_alpha_dummy_437;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0438)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_438 g) from (by
          unfold
            nb078_alpha_dummy_438;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0439
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_425) ≠ (nb078_alpha_dummy_433)
        from (by
          unfold
            nb078_alpha_dummy_433;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0436)
                  0)))) (show (nb078_alpha_dummy_428 g) ≠ (nb078_alpha_dummy_434 g) from (by
          unfold
            nb078_alpha_dummy_434;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0437
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                  unfold nb078_alpha_dummy_421;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                              (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from
                                (by
                                  unfold nb078_alpha_dummy_422;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                              ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                              ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                              ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
                              ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
                              ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                              ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                              ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
                              ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                unfold nb078_alpha_dummy_421;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                            (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from (by
                                unfold nb078_alpha_dummy_422;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                  unfold nb078_alpha_dummy_421;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0420) 0))))
                              (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from
                                (by
                                  unfold nb078_alpha_dummy_422;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0421 g) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                              ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                              ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                              ((nb078_alpha_dummy_443), (nb078_alpha_dummy_444 g)),
                              ((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
                              ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                              ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                              ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
                              ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
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
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0094 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.classMem
        (syn_cop (Class.cv (nb078_alpha_dummy_569)) (Class.cv (nb078_alpha_dummy_571)))
        (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))))
      (Wff.classMem (syn_cop (Class.cv (nb078_alpha_dummy_572 g))
          (Class.cv (nb078_alpha_dummy_574 g))) (syn_ccnv (syn_ccnv (Class.cv g)))) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0084 x y g)))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_614) from (by
                                    unfold nb078_alpha_dummy_614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0658) 1)))) (show
                                  (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_616 g) from (by
                                    unfold nb078_alpha_dummy_616;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0660 g)
                                            1)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from
                                    (by
                                      unfold nb078_alpha_dummy_613;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0658)
                                              0)))) (show
                                    (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_615 g) from
                                    (by
                                      unfold nb078_alpha_dummy_615;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0660 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_643) from (by
                                        unfold nb078_alpha_dummy_643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0662)
                                                0)))) (show (nb078_alpha_dummy_574 g) ≠
                                        (nb078_alpha_dummy_644 g) from (by
                                        unfold nb078_alpha_dummy_644;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0663 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_617) from
                                        (by
                                          unfold nb078_alpha_dummy_617;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0659)
                                                  0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_618 g) from (by
                                          unfold nb078_alpha_dummy_618;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0661 g) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                                    ((Class.cv (nb078_alpha_dummy_571))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                                    ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide))
                                (TAlphaVar.here _ _ _)))
                            (TAlphaClass.cab (nb078_split_alpha_0085 x y g)))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_614) from (by
                                    unfold nb078_alpha_dummy_614;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0658) 1)))) (show
                                  (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_616 g) from (by
                                    unfold nb078_alpha_dummy_616;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0660 g)
                                            1)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from
                                    (by
                                      unfold nb078_alpha_dummy_613;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0658)
                                              0)))) (show
                                    (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_615 g) from
                                    (by
                                      unfold nb078_alpha_dummy_615;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0660 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_643) from (by
                                        unfold nb078_alpha_dummy_643;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0662)
                                                0)))) (show (nb078_alpha_dummy_574 g) ≠
                                        (nb078_alpha_dummy_644 g) from (by
                                        unfold nb078_alpha_dummy_644;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0663 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_617) from
                                        (by
                                          unfold nb078_alpha_dummy_617;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0659)
                                                  0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_618 g) from (by
                                          unfold nb078_alpha_dummy_618;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0661 g) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                                    ((Class.cv (nb078_alpha_dummy_571))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                                    ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide))
                                (TAlphaVar.here _ _ _)))
                            (TAlphaClass.cab (nb078_split_alpha_0085 x y g))))))))))))))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                    (show (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_653) from (by
                        unfold nb078_alpha_dummy_653;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0670) 0)))))
                  (Ne.symm (show (nb078_alpha_dummy_652 g) ≠ (nb078_alpha_dummy_654 g) from (by
                        unfold nb078_alpha_dummy_654;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0671 g) 0)))))
                  (TAlphaVar.there (Ne.symm
                      (show (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_653) from (by
                          unfold nb078_alpha_dummy_653;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0668) 0))))) (Ne.symm
                      (show (nb078_alpha_dummy_651 g) ≠ (nb078_alpha_dummy_654 g) from (by
                          unfold nb078_alpha_dummy_654;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0669 g) 0)))))
                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0086 x y g)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_650) ≠
        (nb078_alpha_dummy_656) from (by
          unfold nb078_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 1)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_658 g) from (by
          unfold nb078_alpha_dummy_658;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_685) from (by
          unfold nb078_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0704) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_686 g) from (by
          unfold nb078_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0705 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_659) from (by
          unfold nb078_alpha_dummy_659;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0701) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_660 g) from (by
          unfold nb078_alpha_dummy_660;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0703 g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_652 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0087 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)), ((nb078_alpha_dummy_656),
        (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
        ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)), ((nb078_alpha_dummy_659),
        (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_650) ≠
        (nb078_alpha_dummy_656) from (by
          unfold nb078_alpha_dummy_656;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 1)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_658 g) from (by
          unfold nb078_alpha_dummy_658;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_655) from (by
          unfold nb078_alpha_dummy_655;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0700) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_657 g) from (by
          unfold nb078_alpha_dummy_657;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0702 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_685) from (by
          unfold nb078_alpha_dummy_685;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0704) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_686 g) from (by
          unfold nb078_alpha_dummy_686;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0705 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_650) ≠ (nb078_alpha_dummy_659) from (by
          unfold nb078_alpha_dummy_659;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0701) 0)))) (show (nb078_alpha_dummy_652 g) ≠
        (nb078_alpha_dummy_660 g) from (by
          unfold nb078_alpha_dummy_660;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0703 g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_649))).fv ∪ ((Class.cv (nb078_alpha_dummy_650))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_651 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_652 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0087 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_687), (nb078_alpha_dummy_688 g)), ((nb078_alpha_dummy_656),
        (nb078_alpha_dummy_658 g)), ((nb078_alpha_dummy_655), (nb078_alpha_dummy_657 g)),
        ((nb078_alpha_dummy_685), (nb078_alpha_dummy_686 g)), ((nb078_alpha_dummy_659),
        (nb078_alpha_dummy_660 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0088 x y g)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_649) ≠
        (nb078_alpha_dummy_692) from (by
          unfold nb078_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 1)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_694 g) from (by
          unfold nb078_alpha_dummy_694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_721) from (by
          unfold nb078_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0742) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_722 g) from (by
          unfold nb078_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0743 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_695) from (by
          unfold nb078_alpha_dummy_695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0739) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_696 g) from (by
          unfold nb078_alpha_dummy_696;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0741 g)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_650))).fv ∪
        ((Class.cv (nb078_alpha_dummy_649))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0089 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)), ((nb078_alpha_dummy_692),
        (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
        ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)), ((nb078_alpha_dummy_695),
        (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_649) ≠
        (nb078_alpha_dummy_692) from (by
          unfold nb078_alpha_dummy_692;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 1)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_694 g) from (by
          unfold nb078_alpha_dummy_694;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_691) from (by
          unfold nb078_alpha_dummy_691;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0738) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_693 g) from (by
          unfold nb078_alpha_dummy_693;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0740 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_721) from (by
          unfold nb078_alpha_dummy_721;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0742) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_722 g) from (by
          unfold nb078_alpha_dummy_722;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0743 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_649) ≠ (nb078_alpha_dummy_695) from (by
          unfold nb078_alpha_dummy_695;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0739) 0)))) (show (nb078_alpha_dummy_651 g) ≠
        (nb078_alpha_dummy_696 g) from (by
          unfold nb078_alpha_dummy_696;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0741 g)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv g))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_650))).fv ∪
        ((Class.cv (nb078_alpha_dummy_649))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_652 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_651 g))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0089 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_723), (nb078_alpha_dummy_724 g)), ((nb078_alpha_dummy_692),
        (nb078_alpha_dummy_694 g)), ((nb078_alpha_dummy_691), (nb078_alpha_dummy_693 g)),
        ((nb078_alpha_dummy_721), (nb078_alpha_dummy_722 g)), ((nb078_alpha_dummy_695),
        (nb078_alpha_dummy_696 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                    (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                              (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_371) from (by
                                  unfold nb078_alpha_dummy_371;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0372) 0)))))
                            (Ne.symm (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_372 g)
                                from (by
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
                              (Ne.symm (show
                                  (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_372 g) from (by
                                    unfold nb078_alpha_dummy_372;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0371 g)
                                            0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078_split_alpha_0090 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078_alpha_dummy_377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_378 g) from (by
          unfold
            nb078_alpha_dummy_378;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0091 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078_alpha_dummy_377;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0403)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_378 g) from (by
          unfold
            nb078_alpha_dummy_378;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0091 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                            (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb078_split_alpha_0092 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_414 g) from (by
          unfold
            nb078_alpha_dummy_414;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0093 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0441)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_414 g) from (by
          unfold
            nb078_alpha_dummy_414;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0093 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_650), (nb078_alpha_dummy_652 g)),
        ((nb078_alpha_dummy_649), (nb078_alpha_dummy_651 g)), ((nb078_alpha_dummy_653),
        (nb078_alpha_dummy_654 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                                          (mem_lt_freshVar (nb078_support_mem_0459 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_650) from
                                    (by
                                      unfold nb078_alpha_dummy_650;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0758)
                                              1)))) (show g ≠ (nb078_alpha_dummy_652 g) from (by
                                      unfold nb078_alpha_dummy_652;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0759 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_649) from (by
                                        unfold nb078_alpha_dummy_649;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0758)
                                                0)))) (show g ≠ (nb078_alpha_dummy_651 g) from
                                      (by
                                        unfold nb078_alpha_dummy_651;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0759 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_653) from
                                        (by
                                          unfold nb078_alpha_dummy_653;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0756)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_654 g) from
                                        (by
                                          unfold nb078_alpha_dummy_654;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0757 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_571) from (by
          unfold nb078_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 2)))) (show g ≠ (nb078_alpha_dummy_574 g) from (by
          unfold nb078_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 2)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_570) from (by
          unfold nb078_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 1)))) (show g ≠ (nb078_alpha_dummy_573 g) from (by
          unfold nb078_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_569) from (by
          unfold nb078_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0752) 0)))) (show g ≠ (nb078_alpha_dummy_572 g) from (by
          unfold nb078_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0754 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_575) from (by
          unfold nb078_alpha_dummy_575;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0753) 0)))) (show g ≠ (nb078_alpha_dummy_576 g) from (by
          unfold nb078_alpha_dummy_576;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0755 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part119`. -/


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
noncomputable def nb078_split_alpha_0095 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_733))
          (Class.cab (nb078_alpha_dummy_727)
            (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                (syn_cphi (Class.cv (nb078_alpha_dummy_728))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_733)) (Class.cab (nb078_alpha_dummy_727)
              (syn_wrex (nb078_alpha_dummy_728) (Class.cv (nb078_alpha_dummy_571))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_727))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_728)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_734 g))
          (Class.cab (nb078_alpha_dummy_729 g)
            (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_734 g))
            (Class.cab (nb078_alpha_dummy_729 g)
              (syn_wrex (nb078_alpha_dummy_730 g) (Class.cv (nb078_alpha_dummy_574 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_729 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_730 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_728) from
                    (by
                      unfold nb078_alpha_dummy_728;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
                  (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_730 g) from (by
                      unfold nb078_alpha_dummy_730;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0762 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_727) from
                      (by
                        unfold nb078_alpha_dummy_727;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 0))))
                    (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_729 g) from (by
                        unfold nb078_alpha_dummy_729;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0762 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_733) from (by
                          unfold nb078_alpha_dummy_733;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0764) 0))))
                      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_734 g) from (by
                          unfold nb078_alpha_dummy_734;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0765 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_731) from (by
                            unfold nb078_alpha_dummy_731;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0761) 0))))
                        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_732 g) from (by
                            unfold nb078_alpha_dummy_732;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0763 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_735) from (by
                              unfold nb078_alpha_dummy_735;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                          (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_737 g) from (by
                              unfold nb078_alpha_dummy_737;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_736) from (by
                                unfold nb078_alpha_dummy_736;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                            (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_738 g) from (by
                                unfold nb078_alpha_dummy_738;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_730 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_742) from (by
          unfold nb078_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_745 g) from (by
          unfold nb078_alpha_dummy_745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_741) from (by
          unfold nb078_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_744 g) from (by
          unfold nb078_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
          unfold nb078_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768) 0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
          unfold nb078_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727),
        (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727),
        (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753) from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753)
        from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠
        (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
                                        unfold nb078_alpha_dummy_739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078_alpha_dummy_737 g) ≠
                                        (nb078_alpha_dummy_740 g) from (by
                                        unfold nb078_alpha_dummy_740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                    ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                    ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                    ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                    ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                    ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
                                    ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                    (by
                                      unfold nb078_alpha_dummy_739;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0768)
                                              0)))) (show
                                    (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_740 g) from
                                    (by
                                      unfold nb078_alpha_dummy_740;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0769 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
                                        unfold nb078_alpha_dummy_739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078_alpha_dummy_737 g) ≠
                                        (nb078_alpha_dummy_740 g) from (by
                                        unfold nb078_alpha_dummy_740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                    ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                    ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                    ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                    ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                    ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
                                    ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
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
                  (TAlphaVar.there (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_728) from
                      (by
                        unfold nb078_alpha_dummy_728;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0760) 1))))
                    (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_730 g) from (by
                        unfold nb078_alpha_dummy_730;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0762 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_727) from (by
                          unfold nb078_alpha_dummy_727;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0760) 0))))
                      (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_729 g) from (by
                          unfold nb078_alpha_dummy_729;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0762 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_733) from (by
                            unfold nb078_alpha_dummy_733;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0764) 0))))
                        (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_734 g) from (by
                            unfold nb078_alpha_dummy_734;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0765 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_731) from (by
                              unfold nb078_alpha_dummy_731;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0761) 0))))
                          (show (nb078_alpha_dummy_574 g) ≠ (nb078_alpha_dummy_732 g) from (by
                              unfold nb078_alpha_dummy_732;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0763 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_571))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_735) from (by
                                unfold nb078_alpha_dummy_735;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0766) 0))))
                            (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_737 g) from (by
                                unfold nb078_alpha_dummy_737;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0767 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_728) ≠ (nb078_alpha_dummy_736) from (by
                                  unfold nb078_alpha_dummy_736;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0766) 1))))
                              (show (nb078_alpha_dummy_730 g) ≠ (nb078_alpha_dummy_738 g) from
                                (by
                                  unfold nb078_alpha_dummy_738;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0767 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_728))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_730 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_742) from (by
          unfold nb078_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 1)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_745 g) from (by
          unfold nb078_alpha_dummy_745;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_741) from (by
          unfold nb078_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0770) 0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_744 g) from (by
          unfold nb078_alpha_dummy_744;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0771 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739)
        from (by
          unfold nb078_alpha_dummy_739;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0768)
                  0)))) (show (nb078_alpha_dummy_737 g) ≠ (nb078_alpha_dummy_740 g) from (by
          unfold nb078_alpha_dummy_740;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0769 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727),
        (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_749) from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0774)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0775
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0772)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0773
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_749)
        from (by
          unfold
            nb078_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0778)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_750 g) from (by
          unfold
            nb078_alpha_dummy_750;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0779
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_747)
        from (by
          unfold
            nb078_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0776)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_748 g) from (by
          unfold
            nb078_alpha_dummy_748;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0777
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_743), (nb078_alpha_dummy_746 g)), ((nb078_alpha_dummy_742),
        (nb078_alpha_dummy_745 g)), ((nb078_alpha_dummy_741), (nb078_alpha_dummy_744 g)),
        ((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)), ((nb078_alpha_dummy_735),
        (nb078_alpha_dummy_737 g)), ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
        ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727),
        (nb078_alpha_dummy_729 g)), ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
        ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_735))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_737
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753) from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_753)
        from (by
          unfold
            nb078_alpha_dummy_753;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0782)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_754 g) from (by
          unfold
            nb078_alpha_dummy_754;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0783
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_742) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0780)
                  0)))) (show (nb078_alpha_dummy_745 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0781
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_735))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_737 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠
        (nb078_alpha_dummy_755) from (by
          unfold
            nb078_alpha_dummy_755;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0786)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_756 g) from (by
          unfold
            nb078_alpha_dummy_756;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0787
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_743) ≠ (nb078_alpha_dummy_751)
        from (by
          unfold
            nb078_alpha_dummy_751;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0784)
                  0)))) (show (nb078_alpha_dummy_746 g) ≠ (nb078_alpha_dummy_752 g) from (by
          unfold
            nb078_alpha_dummy_752;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0785
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
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
                                      (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from (by
                                        unfold nb078_alpha_dummy_739;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0768)
                                                0)))) (show (nb078_alpha_dummy_737 g) ≠
                                        (nb078_alpha_dummy_740 g) from (by
                                        unfold nb078_alpha_dummy_740;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0769 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_735) ≠ (nb078_alpha_dummy_739) from
                                        (by
                                          unfold nb078_alpha_dummy_739;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0768)
                                                  0)))) (show (nb078_alpha_dummy_737 g) ≠
        (nb078_alpha_dummy_740 g) from (by
                                          unfold nb078_alpha_dummy_740;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0769 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_739), (nb078_alpha_dummy_740 g)),
                                      ((nb078_alpha_dummy_735), (nb078_alpha_dummy_737 g)),
                                      ((nb078_alpha_dummy_736), (nb078_alpha_dummy_738 g)),
                                      ((nb078_alpha_dummy_728), (nb078_alpha_dummy_730 g)),
                                      ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
                                      ((nb078_alpha_dummy_733), (nb078_alpha_dummy_734 g)),
                                      ((nb078_alpha_dummy_731), (nb078_alpha_dummy_732 g)),
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
