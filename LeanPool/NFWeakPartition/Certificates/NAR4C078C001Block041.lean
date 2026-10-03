/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block040

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part123`. -/


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
noncomputable def nb078_split_alpha_0099 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_415))
          (Class.cab (nb078_alpha_dummy_409)
            (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                (syn_cphi (Class.cv (nb078_alpha_dummy_410))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_415)) (Class.cab (nb078_alpha_dummy_409)
              (syn_wrex (nb078_alpha_dummy_410) (Class.cv (nb078_alpha_dummy_368))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_409))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_410)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_416 g))
          (Class.cab (nb078_alpha_dummy_411 g)
            (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_416 g))
            (Class.cab (nb078_alpha_dummy_411 g)
              (syn_wrex (nb078_alpha_dummy_412 g) (Class.cv (nb078_alpha_dummy_370 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_411 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_412 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_410) from
                    (by
                      unfold nb078_alpha_dummy_410;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                  (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_412 g) from (by
                      unfold nb078_alpha_dummy_412;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0414 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_409) from
                      (by
                        unfold nb078_alpha_dummy_409;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                    (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_411 g) from (by
                        unfold nb078_alpha_dummy_411;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_415) from (by
                          unfold nb078_alpha_dummy_415;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_416 g) from (by
                          unfold nb078_alpha_dummy_416;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_413) from (by
                            unfold nb078_alpha_dummy_413;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_414 g) from (by
                            unfold nb078_alpha_dummy_414;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_368))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_367))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_369 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
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
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409),
        (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409),
        (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                                    ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                                    ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                                    ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
                                    ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
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
                                    ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                                    ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                                    ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
                                    ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
                                    ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                    ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                    ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
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
                  (TAlphaVar.there (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_410) from
                      (by
                        unfold nb078_alpha_dummy_410;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0412) 1))))
                    (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_412 g) from (by
                        unfold nb078_alpha_dummy_412;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0414 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_409) from (by
                          unfold nb078_alpha_dummy_409;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0412) 0))))
                      (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_411 g) from (by
                          unfold nb078_alpha_dummy_411;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0414 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_415) from (by
                            unfold nb078_alpha_dummy_415;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0416) 0))))
                        (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_416 g) from (by
                            unfold nb078_alpha_dummy_416;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0417 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_413) from (by
                              unfold nb078_alpha_dummy_413;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0413) 0))))
                          (show (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_414 g) from (by
                              unfold nb078_alpha_dummy_414;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0415 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_368))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_367))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_370 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_369 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_412 g) ≠ (nb078_alpha_dummy_420 g) from
                                (by
                                  unfold nb078_alpha_dummy_420;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0419 g) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_410))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_412 g))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_424) from (by
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
                  (nb078_support_mem_0423 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421)
        from (by
          unfold nb078_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0420)
                  0)))) (show (nb078_alpha_dummy_419 g) ≠ (nb078_alpha_dummy_422 g) from (by
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
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409),
        (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409),
        (nb078_alpha_dummy_411 g)), ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368),
        (nb078_alpha_dummy_370 g)), ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                                        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                                      ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                                      ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                                      ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                                      ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                                      ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
                                      ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
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
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_417) ≠ (nb078_alpha_dummy_421) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0421 g) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_421), (nb078_alpha_dummy_422 g)),
                                      ((nb078_alpha_dummy_417), (nb078_alpha_dummy_419 g)),
                                      ((nb078_alpha_dummy_418), (nb078_alpha_dummy_420 g)),
                                      ((nb078_alpha_dummy_410), (nb078_alpha_dummy_412 g)),
                                      ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
                                      ((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
                                      ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
                                      ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
                                      ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
                                      ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
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

/-! Certificates from `NAR4C078C001Part124`. -/


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
noncomputable def nb078_split_alpha_0100 (x : Var) (y : Var) (g : Var) :
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
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
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
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0101 (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    TAlphaWff
      [((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (syn_wf (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_004))
          (Class.cv (nb078_alpha_dummy_003)))
        (Wff.neg (syn_wfun (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))))
      (Wff.imp (syn_wf (Class.cv g) (Class.cv y) (Class.cv x))
        (Wff.neg (syn_wfun (syn_ccnv (Class.cv g))))) :=
  (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.neg (nb078_split_alpha_0057 x y g dv_g_y))
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                    ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                    ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0058 x y g))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
          unfold
            nb078_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
          unfold
            nb078_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529)
        from (by
          unfold
            nb078_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold
            nb078_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_559)
        from (by
          unfold
            nb078_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_560 g) from (by
          unfold
            nb078_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_533)
        from (by
          unfold
            nb078_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_534 g) from (by
          unfold
            nb078_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078_split_alpha_0059 x y g))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
          unfold
            nb078_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
          unfold
            nb078_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529)
        from (by
          unfold
            nb078_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold
            nb078_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_559)
        from (by
          unfold
            nb078_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_560 g) from (by
          unfold
            nb078_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_533)
        from (by
          unfold
            nb078_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_534 g) from (by
          unfold
            nb078_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078_split_alpha_0059 x y g)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_526) from (by
                                        unfold nb078_alpha_dummy_526;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0582)
                                                1)))) (show g ≠ (nb078_alpha_dummy_528 g) from
                                      (by
                                        unfold nb078_alpha_dummy_528;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0583 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_525) from
                                        (by
                                          unfold nb078_alpha_dummy_525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0582)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_527 g) from
                                        (by
                                          unfold nb078_alpha_dummy_527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0583 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_523) from (by
          unfold nb078_alpha_dummy_523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0580) 0)))) (show g ≠ (nb078_alpha_dummy_524 x g) from (by
          unfold nb078_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0581 x g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_521) from (by
          unfold nb078_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0578) 0)))) (show g ≠ (nb078_alpha_dummy_522 x g) from (by
          unfold nb078_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0579 x g) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_523) from (by
                                unfold nb078_alpha_dummy_523;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0586) 0))))
                            (show x ≠ (nb078_alpha_dummy_524 x g) from (by
                                unfold nb078_alpha_dummy_524;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0587 x g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_521) from (by
                                  unfold nb078_alpha_dummy_521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0584) 0))))
                              (show x ≠ (nb078_alpha_dummy_522 x g) from (by
                                  unfold nb078_alpha_dummy_522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0585 x g)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_g_x) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                    ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                    ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cvv) (by simp only [fv_syn_cvv]))) (TAlphaWff.classMem
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0058 x y g))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
          unfold
            nb078_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
          unfold
            nb078_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529)
        from (by
          unfold
            nb078_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold
            nb078_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_559)
        from (by
          unfold
            nb078_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_560 g) from (by
          unfold
            nb078_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_533)
        from (by
          unfold
            nb078_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_534 g) from (by
          unfold
            nb078_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078_split_alpha_0059 x y g))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
          unfold
            nb078_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  1)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
          unfold
            nb078_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529)
        from (by
          unfold
            nb078_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0568)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
          unfold
            nb078_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0570
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_559)
        from (by
          unfold
            nb078_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0572)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_560 g) from (by
          unfold
            nb078_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0573
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_533)
        from (by
          unfold
            nb078_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0569)
                  0)))) (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_534 g) from (by
          unfold
            nb078_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0571
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (by decide)) (freshVar_injective
        (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_526))).fv ∪ ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb078_split_alpha_0059 x y g)))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_526) from (by
                                        unfold nb078_alpha_dummy_526;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0582)
                                                1)))) (show g ≠ (nb078_alpha_dummy_528 g) from
                                      (by
                                        unfold nb078_alpha_dummy_528;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0583 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_525) from
                                        (by
                                          unfold nb078_alpha_dummy_525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0582)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_527 g) from
                                        (by
                                          unfold nb078_alpha_dummy_527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0583 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_523) from (by
          unfold nb078_alpha_dummy_523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0580) 0)))) (show g ≠ (nb078_alpha_dummy_524 x g) from (by
          unfold nb078_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0581 x g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_521) from (by
          unfold nb078_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0578) 0)))) (show g ≠ (nb078_alpha_dummy_522 x g) from (by
          unfold nb078_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0579 x g) 0)))) (TAlphaVar.here _ _ _)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_523) from (by
                                unfold nb078_alpha_dummy_523;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0586) 0))))
                            (show x ≠ (nb078_alpha_dummy_524 x g) from (by
                                unfold nb078_alpha_dummy_524;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0587 x g) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_003) ≠ (nb078_alpha_dummy_521) from (by
                                  unfold nb078_alpha_dummy_521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0584) 0))))
                              (show x ≠ (nb078_alpha_dummy_522 x g) from (by
                                  unfold nb078_alpha_dummy_522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0585 x g)
                                          0)))) (TAlphaVar.there
                                (freshVar_injective ((∅ : Finset Var)) (by decide))
                                (Ne.symm dv_g_x) (TAlphaVar.there
                                  (freshVar_injective ((∅ : Finset Var)) (by decide))
                                  dv_x_y (TAlphaVar.here _ _ _)))))))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_cvv) (by simp only [fv_syn_cvv])))
              (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0061 x y g))))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_526) from (by
                        unfold nb078_alpha_dummy_526;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0582) 1))))
                    (show g ≠ (nb078_alpha_dummy_528 g) from (by
                        unfold nb078_alpha_dummy_528;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0583 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_525) from (by
                          unfold nb078_alpha_dummy_525;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0582) 0))))
                      (show g ≠ (nb078_alpha_dummy_527 g) from (by
                          unfold nb078_alpha_dummy_527;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0583 g) 0))))
                      (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078_split_alpha_0081 x y g))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn
                          [((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cid) (nb078_wpp_refl_0273 x y g)))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
                              (TAlphaWff.neg (nb078_split_alpha_0081 x y g))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_reflOn
                          [((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cid) (nb078_wpp_refl_0273 x y g)))))))))) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (Ne.symm
                        (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_575) from (by
                            unfold nb078_alpha_dummy_575;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0590) 0))))) (Ne.symm
                        (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_576 g) from (by
                            unfold nb078_alpha_dummy_576;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0591 g) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_575) from (by
                              unfold nb078_alpha_dummy_575;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0588) 0))))) (Ne.symm
                          (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_576 g) from (by
                              unfold nb078_alpha_dummy_576;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0589 g) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb078_split_alpha_0082 x y g)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex
                                      (TAlphaWff.neg (nb078_split_alpha_0083 x y g)))))
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg
                                        (nb078_split_alpha_0083 x y g))))))))))))) (TAlphaWff.ex
                  (TAlphaWff.conj (nb078_split_alpha_0094 x y g) (TAlphaWff.classMem
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0095 x y g)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_728) from (by
          unfold nb078_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  1)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_730 g) from (by
          unfold nb078_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727)
        from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_757)
        from (by
          unfold nb078_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_758 g) from (by
          unfold nb078_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_731)
        from (by
          unfold nb078_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_732 g) from (by
          unfold nb078_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0096 x y g)))))))
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_728) from (by
          unfold nb078_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  1)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_730 g) from (by
          unfold nb078_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727)
        from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_757)
        from (by
          unfold nb078_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_758 g) from (by
          unfold nb078_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_731)
        from (by
          unfold nb078_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789)
                  0)))) (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_732 g) from (by
          unfold nb078_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791
                    g)
                  0)))) (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
        (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective (((syn_ccnv
        (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv
        (nb078_alpha_dummy_570))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_574 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (nb078_split_alpha_0096 x y g))))))))))))))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm (show
                                        (nb078_alpha_dummy_368) ≠ (nb078_alpha_dummy_371) from
                                        (by
                                          unfold nb078_alpha_dummy_371;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0372)
                                                  0))))) (Ne.symm (show
                                        (nb078_alpha_dummy_370 g) ≠ (nb078_alpha_dummy_372 g)
                                        from (by
                                          unfold nb078_alpha_dummy_372;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0373 g) 0)))))
                                    (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_367) ≠
        (nb078_alpha_dummy_371) from (by
          unfold nb078_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0370) 0))))) (Ne.symm (show (nb078_alpha_dummy_369 g) ≠
        (nb078_alpha_dummy_372 g) from (by
          unfold nb078_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0371 g) 0))))) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                                  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0097 x y g))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0098 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0098 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0099 x y g))))) (TAlphaWff.classMem
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0100 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0100 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003),
        x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_368) from (by
                                        unfold nb078_alpha_dummy_368;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0460)
                                                1)))) (show g ≠ (nb078_alpha_dummy_370 g) from
                                      (by
                                        unfold nb078_alpha_dummy_370;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0461 g)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_367) from
                                        (by
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
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0461 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_371) from (by
          unfold nb078_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0458) 0)))) (show g ≠ (nb078_alpha_dummy_372 g) from (by
          unfold nb078_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0459 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_571) from (by
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
                  (nb078_support_mem_0755 g)
                  0)))) (TAlphaVar.here _ _ _))))))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
