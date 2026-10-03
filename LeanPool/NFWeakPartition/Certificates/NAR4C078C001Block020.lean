/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block019

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part066`. -/


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
noncomputable def nb078_split_alpha_0036 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_415), (nb078_alpha_dummy_416 g)),
        ((nb078_alpha_dummy_413), (nb078_alpha_dummy_414 g)),
        ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)),
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                    ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                    ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                    ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                    ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                    ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                    ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_417))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_419
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_417))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_419 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part067`. -/


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
noncomputable def nb078_split_alpha_0037 (x : Var) (y : Var) (g : Var) :
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
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
                                        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287),
        (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283),
        (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                            ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                            ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                            ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                            ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                            ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                            ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
                            ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                            ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                            ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                            ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                            ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                            ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
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
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288),
        (nb078_alpha_dummy_291 g)), ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285),
        (nb078_alpha_dummy_286 g)), ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
                              ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                              ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                              ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                              ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                              ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                              ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part068`. -/


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
noncomputable def nb078_split_alpha_0038 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
        ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
        ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
        ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
        ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_451))
          (Class.cab (nb078_alpha_dummy_445)
            (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                (syn_cphi (Class.cv (nb078_alpha_dummy_446))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_451)) (Class.cab (nb078_alpha_dummy_445)
              (syn_wrex (nb078_alpha_dummy_446) (Class.cv (nb078_alpha_dummy_289))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_445))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_446)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_452 g))
          (Class.cab (nb078_alpha_dummy_447 g)
            (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_452 g))
            (Class.cab (nb078_alpha_dummy_447 g)
              (syn_wrex (nb078_alpha_dummy_448 g) (Class.cv (nb078_alpha_dummy_292 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_447 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_448 g))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_446) from
                    (by
                      unfold nb078_alpha_dummy_446;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
                  (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_448 g) from (by
                      unfold nb078_alpha_dummy_448;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0464 g) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_445) from
                      (by
                        unfold nb078_alpha_dummy_445;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 0))))
                    (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_447 g) from (by
                        unfold nb078_alpha_dummy_447;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0464 g) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_451) from (by
                          unfold nb078_alpha_dummy_451;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0466) 0))))
                      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_452 g) from (by
                          unfold nb078_alpha_dummy_452;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0467 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_449) from (by
                            unfold nb078_alpha_dummy_449;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0463) 0))))
                        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_450 g) from (by
                            unfold nb078_alpha_dummy_450;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0465 g) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_289))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_446))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_448 g))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_453) ≠ (nb078_alpha_dummy_460) from (by
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
                  (nb078_support_mem_0471 g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_461), (nb078_alpha_dummy_464 g)), ((nb078_alpha_dummy_460),
        (nb078_alpha_dummy_463 g)), ((nb078_alpha_dummy_459), (nb078_alpha_dummy_462 g)),
        ((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)), ((nb078_alpha_dummy_453),
        (nb078_alpha_dummy_455 g)), ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
        ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445),
        (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445),
        (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_455 g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_453))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_455 g))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
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
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                    ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                    ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                    ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                    ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                    ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
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
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
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
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_457), (nb078_alpha_dummy_458 g)),
                                    ((nb078_alpha_dummy_453), (nb078_alpha_dummy_455 g)),
                                    ((nb078_alpha_dummy_454), (nb078_alpha_dummy_456 g)),
                                    ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                    ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                    ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
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
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_446) from
                      (by
                        unfold nb078_alpha_dummy_446;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0462) 1))))
                    (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_448 g) from (by
                        unfold nb078_alpha_dummy_448;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0464 g) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_445) from (by
                          unfold nb078_alpha_dummy_445;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0462) 0))))
                      (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_447 g) from (by
                          unfold nb078_alpha_dummy_447;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0464 g) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_451) from (by
                            unfold nb078_alpha_dummy_451;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0466) 0))))
                        (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_452 g) from (by
                            unfold nb078_alpha_dummy_452;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0467 g) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_289) ≠ (nb078_alpha_dummy_449) from (by
                              unfold nb078_alpha_dummy_449;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0463) 0))))
                          (show (nb078_alpha_dummy_292 g) ≠ (nb078_alpha_dummy_450 g) from (by
                              unfold nb078_alpha_dummy_450;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0465 g) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_289))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_288))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_292 g))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_291 g))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
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
        ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445),
        (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)), ((nb078_alpha_dummy_445),
        (nb078_alpha_dummy_447 g)), ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
        ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)), ((nb078_alpha_dummy_289),
        (nb078_alpha_dummy_292 g)), ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
        ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)), ((nb078_alpha_dummy_293),
        (nb078_alpha_dummy_294 g)), ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
        ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)), ((nb078_alpha_dummy_001), g),
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
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
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
                                      ((nb078_alpha_dummy_446), (nb078_alpha_dummy_448 g)),
                                      ((nb078_alpha_dummy_445), (nb078_alpha_dummy_447 g)),
                                      ((nb078_alpha_dummy_451), (nb078_alpha_dummy_452 g)),
                                      ((nb078_alpha_dummy_449), (nb078_alpha_dummy_450 g)),
                                      ((nb078_alpha_dummy_289), (nb078_alpha_dummy_292 g)),
                                      ((nb078_alpha_dummy_288), (nb078_alpha_dummy_291 g)),
                                      ((nb078_alpha_dummy_287), (nb078_alpha_dummy_290 g)),
                                      ((nb078_alpha_dummy_293), (nb078_alpha_dummy_294 g)),
                                      ((nb078_alpha_dummy_285), (nb078_alpha_dummy_286 g)),
                                      ((nb078_alpha_dummy_283), (nb078_alpha_dummy_284 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
