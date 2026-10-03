/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block025

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part085`. -/


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
noncomputable def nb078_split_alpha_0056 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
        ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
        ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_441))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_410))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_441)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_442 g))
          (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_442 g))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_417) from (by
                              unfold nb078_alpha_dummy_417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                          (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_419 g) from (by
                              unfold nb078_alpha_dummy_419;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                          (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_444 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0446) 0)))) (show
                                  (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_442 g) from (by
                                    unfold nb078_alpha_dummy_442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0447 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_424) from (by
          unfold nb078_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_427 g) from (by
          unfold nb078_alpha_dummy_427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_423) from (by
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
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_435) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                        unfold nb078_alpha_dummy_421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078_alpha_dummy_419 g) ≠
                                        (nb078_alpha_dummy_422 g) from (by
                                        unfold nb078_alpha_dummy_422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
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
                                    ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from
                                    (by
                                      unfold nb078_alpha_dummy_421;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0420)
                                              0)))) (show
                                    (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from
                                    (by
                                      unfold nb078_alpha_dummy_422;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0421 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                        unfold nb078_alpha_dummy_421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078_alpha_dummy_419 g) ≠
                                        (nb078_alpha_dummy_422 g) from (by
                                        unfold nb078_alpha_dummy_422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
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
                                    ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_410) ≠ (nb078_alpha_dummy_417) from (by
                              unfold nb078_alpha_dummy_417;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0418) 0))))
                          (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_419 g) from (by
                              unfold nb078_alpha_dummy_419;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0419 g) 0))))
                          (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_444 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0446) 0)))) (show
                                  (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_442 g) from (by
                                    unfold nb078_alpha_dummy_442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0447 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_412 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_424) from (by
          unfold nb078_alpha_dummy_424;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0422) 1)))) (show (nb078_alpha_dummy_419 g) ≠
        (nb078_alpha_dummy_427 g) from (by
          unfold nb078_alpha_dummy_427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0423 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_423) from (by
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
                  (nb078_support_mem_0421 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
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
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)), ((nb078_alpha_dummy_481),
        (nb078_alpha_dummy_483 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_424) ≠ (nb078_alpha_dummy_435) from (by
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
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                        unfold nb078_alpha_dummy_421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078_alpha_dummy_419 g) ≠
                                        (nb078_alpha_dummy_422 g) from (by
                                        unfold nb078_alpha_dummy_422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
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
                                    ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from
                                    (by
                                      unfold nb078_alpha_dummy_421;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0420)
                                              0)))) (show
                                    (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from
                                    (by
                                      unfold nb078_alpha_dummy_422;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0421 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from (by
                                        unfold nb078_alpha_dummy_421;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0420)
                                                0)))) (show (nb078_alpha_dummy_419 g) ≠
                                        (nb078_alpha_dummy_422 g) from (by
                                        unfold nb078_alpha_dummy_422;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0421 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
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
                                    ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)),
            ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
            ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
            ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)),
            ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
            ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
            ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
            ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
            ((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
            ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb078_split_alpha_0057 (x : Var) (y : Var) (g : Var) (dv_g_y : g ≠ y) :
    TAlphaWff
      [((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (syn_wfun (Class.cv (nb078_alpha_dummy_001))) (Wff.neg
          (Wff.classEq (syn_cdm (Class.cv (nb078_alpha_dummy_001)))
            (Class.cv (nb078_alpha_dummy_004)))))
      (Wff.imp (syn_wfun (Class.cv g))
        (Wff.neg (Wff.classEq (syn_cdm (Class.cv g)) (Class.cv y)))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0040 x y g))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                          ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                          ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0136 x y g)))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex
                          (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0040 x y g))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_reflOn
                        [((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                          ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                          ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                          ((nb078_alpha_dummy_003), x)]
                        (syn_cid) (nb078_wpp_refl_0136 x y g)))))))))) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_293) from (by
                          unfold nb078_alpha_dummy_293;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0292) 0))))) (Ne.symm
                      (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_294 g) from (by
                          unfold nb078_alpha_dummy_294;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0293 g) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_293) from (by
                            unfold nb078_alpha_dummy_293;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0290) 0))))) (Ne.symm
                        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_294 g) from (by
                            unfold nb078_alpha_dummy_294;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0291 g) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0041 x y g)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb078_split_alpha_0042 x y g)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                      (nb078_split_alpha_0042 x y g))))))))))))) (TAlphaWff.ex
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                        (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0043 x y g)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_332) from (by
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
                  (nb078_support_mem_0362 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331)
        from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_361)
        from (by
          unfold nb078_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_362 g) from (by
          unfold nb078_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_335)
        from (by
          unfold nb078_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_336 g) from (by
          unfold nb078_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
        ((Class.cv (nb078_alpha_dummy_289))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0044 x y g)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_332) from (by
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
                  (nb078_support_mem_0362 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_331)
        from (by
          unfold nb078_alpha_dummy_331;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0360)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_333 g) from (by
          unfold nb078_alpha_dummy_333;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0362 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_361)
        from (by
          unfold nb078_alpha_dummy_361;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0364)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_362 g) from (by
          unfold nb078_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0365 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_335)
        from (by
          unfold nb078_alpha_dummy_335;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0361)
                  0)))) (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_336 g) from (by
          unfold nb078_alpha_dummy_336;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0363
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_287))).fv ∪
        ((Class.cv (nb078_alpha_dummy_289))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_292 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0044 x y g))))))))))))))
                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                      (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_371) from (by
                                        unfold nb078_alpha_dummy_371;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0372)
                                                0))))) (Ne.symm (show
                                      (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_372 g) from
                                      (by
                                        unfold nb078_alpha_dummy_372;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0373 g)
                                                0))))) (TAlphaVar.there (Ne.symm (show
                                        (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_371) from
                                        (by
                                          unfold nb078_alpha_dummy_371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0370)
                                                  0))))) (Ne.symm (show
                                        (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_372 g)
                                        from (by
                                          unfold nb078_alpha_dummy_372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0371 g) 0)))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0045 x y g))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_374) from (by
          unfold
            nb078_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
          unfold
            nb078_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373)
        from (by
          unfold
            nb078_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold
            nb078_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_403)
        from (by
          unfold
            nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold
            nb078_alpha_dummy_404;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0046 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠
        (nb078_alpha_dummy_374) from (by
          unfold
            nb078_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  1)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_376 g) from (by
          unfold
            nb078_alpha_dummy_376;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_373)
        from (by
          unfold
            nb078_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0402)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_375 g) from (by
          unfold
            nb078_alpha_dummy_375;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0404
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_403)
        from (by
          unfold
            nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold
            nb078_alpha_dummy_404;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0046 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0047 x y g))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_410) from (by
          unfold
            nb078_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
          unfold
            nb078_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409)
        from (by
          unfold
            nb078_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold
            nb078_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_439)
        from (by
          unfold
            nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold
            nb078_alpha_dummy_440;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0048 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠
        (nb078_alpha_dummy_410) from (by
          unfold
            nb078_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  1)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_412 g) from (by
          unfold
            nb078_alpha_dummy_412;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_409)
        from (by
          unfold
            nb078_alpha_dummy_409;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0440)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_411 g) from (by
          unfold
            nb078_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0442
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_439)
        from (by
          unfold
            nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold
            nb078_alpha_dummy_440;
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0048 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_368) from
                                    (by
                                      unfold nb078_alpha_dummy_368;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0460)
                                              1)))) (show g ≠ (nb078_alpha_dummy_370 g) from (by
                                      unfold nb078_alpha_dummy_370;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0461 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_367) from (by
                                        unfold nb078_alpha_dummy_367;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0460)
                                                0)))) (show g ≠ (nb078_alpha_dummy_369 g) from
                                      (by
                                        unfold nb078_alpha_dummy_369;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0461 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_371) from
                                        (by
                                          unfold nb078_alpha_dummy_371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0458)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_372 g) from
                                        (by
                                          unfold nb078_alpha_dummy_372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0459 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_289) from (by
          unfold nb078_alpha_dummy_289;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 2)))) (show g ≠ (nb078_alpha_dummy_292 g) from (by
          unfold nb078_alpha_dummy_292;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 2)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_288) from (by
          unfold nb078_alpha_dummy_288;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 1)))) (show g ≠ (nb078_alpha_dummy_291 g) from (by
          unfold nb078_alpha_dummy_291;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_287) from (by
          unfold nb078_alpha_dummy_287;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0454) 0)))) (show g ≠ (nb078_alpha_dummy_290 g) from (by
          unfold nb078_alpha_dummy_290;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0456 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_293) from (by
          unfold nb078_alpha_dummy_293;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0455) 0)))) (show g ≠ (nb078_alpha_dummy_294 g) from (by
          unfold nb078_alpha_dummy_294;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0457 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.neg (nb078_split_alpha_0049 x y g)))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_446) from (by
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
                  (nb078_support_mem_0492 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445)
        from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_475)
        from (by
          unfold nb078_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_476 g) from (by
          unfold nb078_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_449)
        from (by
          unfold nb078_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_450 g) from (by
          unfold nb078_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_289))).fv ∪
        ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0050 x y g)))))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_446) from (by
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
                  (nb078_support_mem_0492 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_445)
        from (by
          unfold nb078_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0490)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_447 g) from (by
          unfold nb078_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0492 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_475)
        from (by
          unfold nb078_alpha_dummy_475;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0494)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_476 g) from (by
          unfold nb078_alpha_dummy_476;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0495 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_288) ≠ (nb078_alpha_dummy_449)
        from (by
          unfold nb078_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0491)
                  0)))) (show (nb078_alpha_dummy_291 g) ≠ (nb078_alpha_dummy_450 g) from (by
          unfold nb078_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0493
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv)
        (by decide)) (freshVar_injective (((Class.cv g)).fv ∪ ((syn_ccnv (Class.cv g))).fv)
        (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_289))).fv ∪
        ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_292 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0050 x y g))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.there
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
                                  (mem_lt_freshVar (nb078_support_mem_0456 g) 2))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_288) from (by
                              unfold nb078_alpha_dummy_288;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0454) 1))))
                          (show g ≠ (nb078_alpha_dummy_291 g) from (by
                              unfold nb078_alpha_dummy_291;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0456 g) 1))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_287) from (by
                                unfold nb078_alpha_dummy_287;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0454) 0))))
                            (show g ≠ (nb078_alpha_dummy_290 g) from (by
                                unfold nb078_alpha_dummy_290;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0456 g) 0))))
                            (TAlphaVar.there
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
                              (TAlphaVar.here _ _ _)))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_482), (nb078_alpha_dummy_484 g)),
                    ((nb078_alpha_dummy_481), (nb078_alpha_dummy_483 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_cvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0052 x y g))))
                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                          (TAlphaClass.cv (TAlphaVar.there (Ne.symm
                                (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_371) from (by
                                    unfold nb078_alpha_dummy_371;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0372) 0)))))
                              (Ne.symm (show
                                  (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_372 g) from (by
                                    unfold nb078_alpha_dummy_372;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0373 g)
                                            0))))) (TAlphaVar.there (Ne.symm
                                  (show (nb078_alpha_dummy_367) ≠ (nb078_alpha_dummy_371) from
                                    (by
                                      unfold nb078_alpha_dummy_371;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0370)
                                              0))))) (Ne.symm (show
                                    (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_372 g) from
                                    (by
                                      unfold nb078_alpha_dummy_372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0371 g)
                                              0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0053 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold
            nb078_alpha_dummy_404;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0054 x y g))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0404
                    g)
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
          unfold
            nb078_alpha_dummy_403;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0406)
                  0)))) (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_404 g) from (by
          unfold
            nb078_alpha_dummy_404;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0054 x y g))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb078_split_alpha_0055 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold
            nb078_alpha_dummy_440;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0056 x y g))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                  (nb078_support_mem_0442
                    g)
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
          unfold
            nb078_alpha_dummy_439;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0444)
                  0)))) (show (nb078_alpha_dummy_369 g) ≠ (nb078_alpha_dummy_440 g) from (by
          unfold
            nb078_alpha_dummy_440;
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
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
        (nb078_split_alpha_0056 x y g)))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
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
                                          (mem_lt_freshVar (nb078_support_mem_0461 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_371) from
                                    (by
                                      unfold nb078_alpha_dummy_371;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0458)
                                              0)))) (show g ≠ (nb078_alpha_dummy_372 g) from (by
                                      unfold nb078_alpha_dummy_372;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0459 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_482) from (by
                                        unfold nb078_alpha_dummy_482;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0538)
                                                1)))) (show g ≠ (nb078_alpha_dummy_484 g) from
                                      (by
                                        unfold nb078_alpha_dummy_484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0539 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_481) from
                                        (by
                                          unfold nb078_alpha_dummy_481;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0538)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_483 g) from
                                        (by
                                          unfold nb078_alpha_dummy_483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0539 g) 0))))
                                      (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
            (Ne.symm dv_g_y) (TAlphaVar.here _ _ _))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part086`. -/


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
noncomputable def nb078_split_alpha_0058 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_535))
          (Class.cab (nb078_alpha_dummy_529)
            (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                (syn_cphi (Class.cv (nb078_alpha_dummy_530))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_535)) (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_536 g))
          (Class.cab (nb078_alpha_dummy_531 g)
            (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_536 g))
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from
                    (by
                      unfold nb078_alpha_dummy_530;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                  (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
                      unfold nb078_alpha_dummy_532;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_529) from
                      (by
                        unfold nb078_alpha_dummy_529;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                    (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_531 g) from (by
                        unfold nb078_alpha_dummy_531;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0542 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_535) from (by
                          unfold nb078_alpha_dummy_535;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                      (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_536 g) from (by
                          unfold nb078_alpha_dummy_536;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_533) from (by
                            unfold nb078_alpha_dummy_533;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0541) 0))))
                        (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_534 g) from (by
                            unfold nb078_alpha_dummy_534;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0543 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_526))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from (by
                              unfold nb078_alpha_dummy_537;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                          (show (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_539 g) from (by
                              unfold nb078_alpha_dummy_539;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from (by
                                unfold nb078_alpha_dummy_538;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                            (show (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_540 g) from (by
                                unfold nb078_alpha_dummy_540;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_532 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_544) from (by
          unfold nb078_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543) from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
          unfold nb078_alpha_dummy_541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_542 g) from (by
          unfold nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529),
        (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526),
        (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521),
        (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_551) from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_551)
        from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_551) from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_551)
        from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529),
        (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526),
        (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521),
        (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠
        (nb078_alpha_dummy_555) from (by
          unfold
            nb078_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_556 g) from (by
          unfold
            nb078_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555)
        from (by
          unfold
            nb078_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_556 g) from (by
          unfold
            nb078_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_557) from (by
          unfold
            nb078_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_558 g) from (by
          unfold
            nb078_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_557) from (by
          unfold
            nb078_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_558 g) from (by
          unfold
            nb078_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
                                        unfold nb078_alpha_dummy_541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078_alpha_dummy_539 g) ≠
                                        (nb078_alpha_dummy_542 g) from (by
                                        unfold nb078_alpha_dummy_542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
                                    ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
                                    ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
                                    ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                    ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                    ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
                                    ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                    ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                    ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                    ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from
                                    (by
                                      unfold nb078_alpha_dummy_541;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0548)
                                              0)))) (show
                                    (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_542 g) from
                                    (by
                                      unfold nb078_alpha_dummy_542;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0549 g)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
                                        unfold nb078_alpha_dummy_541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078_alpha_dummy_539 g) ≠
                                        (nb078_alpha_dummy_542 g) from (by
                                        unfold nb078_alpha_dummy_542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
                                    ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
                                    ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
                                    ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                    ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                    ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
                                    ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                    ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                    ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                    ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from
                      (by
                        unfold nb078_alpha_dummy_530;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                    (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
                        unfold nb078_alpha_dummy_532;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0542 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_529) from (by
                          unfold nb078_alpha_dummy_529;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0540) 0))))
                      (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_531 g) from (by
                          unfold nb078_alpha_dummy_531;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0542 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_535) from (by
                            unfold nb078_alpha_dummy_535;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0544) 0))))
                        (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_536 g) from (by
                            unfold nb078_alpha_dummy_536;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0545 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_533) from (by
                              unfold nb078_alpha_dummy_533;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0541) 0))))
                          (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_534 g) from (by
                              unfold nb078_alpha_dummy_534;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0543 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_526))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from (by
                                unfold nb078_alpha_dummy_537;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0546) 0))))
                            (show (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_539 g) from (by
                                unfold nb078_alpha_dummy_539;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0547 g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from (by
                                  unfold nb078_alpha_dummy_538;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0546) 1))))
                              (show (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_540 g) from
                                (by
                                  unfold nb078_alpha_dummy_540;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0547 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_530))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_532 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_544) from (by
          unfold nb078_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 1)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543) from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550) 0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541)
        from (by
          unfold nb078_alpha_dummy_541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_542 g) from (by
          unfold nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529),
        (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526),
        (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521),
        (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_551) from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_551)
        from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_551) from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0554)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0555
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0552)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0553
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_551)
        from (by
          unfold
            nb078_alpha_dummy_551;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0558)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_552 g) from (by
          unfold
            nb078_alpha_dummy_552;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0559
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_549)
        from (by
          unfold
            nb078_alpha_dummy_549;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0556)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_550 g) from (by
          unfold
            nb078_alpha_dummy_550;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0557
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529),
        (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526),
        (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)), ((nb078_alpha_dummy_521),
        (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠
        (nb078_alpha_dummy_555) from (by
          unfold
            nb078_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_556 g) from (by
          unfold
            nb078_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555)
        from (by
          unfold
            nb078_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0562)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_556 g) from (by
          unfold
            nb078_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0563
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0560)
                  0)))) (show (nb078_alpha_dummy_547 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0561
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_557) from (by
          unfold
            nb078_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_558 g) from (by
          unfold
            nb078_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_557) from (by
          unfold
            nb078_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0566)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_558 g) from (by
          unfold
            nb078_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0567
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠ (nb078_alpha_dummy_553)
        from (by
          unfold
            nb078_alpha_dummy_553;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0564)
                  0)))) (show (nb078_alpha_dummy_548 g) ≠ (nb078_alpha_dummy_554 g) from (by
          unfold
            nb078_alpha_dummy_554;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0565
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from
                                        (by
                                          unfold nb078_alpha_dummy_541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_542 g) from (by
                                          unfold nb078_alpha_dummy_542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
                                      ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
                                      ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
                                      ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                      ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                      ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                      ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                      ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
                                        unfold nb078_alpha_dummy_541;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0548)
                                                0)))) (show (nb078_alpha_dummy_539 g) ≠
                                        (nb078_alpha_dummy_542 g) from (by
                                        unfold nb078_alpha_dummy_542;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0549 g)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from
                                        (by
                                          unfold nb078_alpha_dummy_541;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0548)
                                                  0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_542 g) from (by
                                          unfold nb078_alpha_dummy_542;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0549 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
                                      ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
                                      ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)),
                                      ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                      ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                      ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                      ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                      ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
