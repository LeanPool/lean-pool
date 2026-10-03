/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block033

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part105`. -/


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
noncomputable def nb078_split_alpha_0079 (x : Var) (y : Var) (g : Var) :
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
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
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
                                    ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                    ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                    ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                    ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                                    ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                    ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_371), (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571),
        (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575),
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
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
                                      ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                                      ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                                      ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                                      ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                                      ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                      ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part106`. -/


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
noncomputable def nb078_split_alpha_0080 (x : Var) (y : Var) (g : Var) :
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
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                                        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                                        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                            ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                            ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
        (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)), ((nb078_alpha_dummy_570),
        (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)), ((nb078_alpha_dummy_567),
        (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                              ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
                              ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
                              ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
                              ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
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
                              ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
                              ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
                              ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb078_split_alpha_0081 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)),
        ((nb078_alpha_dummy_569), (nb078_alpha_dummy_572 g)),
        ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_575))
          (syn_cop (Class.cv (nb078_alpha_dummy_569)) (Class.cv (nb078_alpha_dummy_570))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_571) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_569))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_001))))
                (Class.cv (nb078_alpha_dummy_571))) (syn_wbr (Class.cv (nb078_alpha_dummy_571))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_570)))))))
      (Wff.imp (Wff.classEq (Class.cv (nb078_alpha_dummy_576 g))
          (syn_cop (Class.cv (nb078_alpha_dummy_572 g)) (Class.cv (nb078_alpha_dummy_573 g))))
        (Wff.neg (syn_wex (nb078_alpha_dummy_574 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_572 g))
                (syn_ccnv (syn_ccnv (Class.cv g))) (Class.cv (nb078_alpha_dummy_574 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_574 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_573 g))))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_575) from (by
                unfold nb078_alpha_dummy_575;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0590) 0))))) (Ne.symm
            (show (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_576 g) from (by
                unfold nb078_alpha_dummy_576;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0591 g) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb078_alpha_dummy_569) ≠ (nb078_alpha_dummy_575) from
                (by
                  unfold nb078_alpha_dummy_575;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0588) 0)))))
            (Ne.symm (show (nb078_alpha_dummy_572 g) ≠ (nb078_alpha_dummy_576 g) from (by
                  unfold nb078_alpha_dummy_576;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0589 g) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0062 x y g)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_578) from
                                    (by
                                      unfold nb078_alpha_dummy_578;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0620)
                                              1)))) (show
                                    (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_580 g) from
                                    (by
                                      unfold nb078_alpha_dummy_580;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0622 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_577) from (by
                                        unfold nb078_alpha_dummy_577;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0620)
                                                0)))) (show (nb078_alpha_dummy_573 g) ≠
                                        (nb078_alpha_dummy_579 g) from (by
                                        unfold nb078_alpha_dummy_579;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0622 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_607) from
                                        (by
                                          unfold nb078_alpha_dummy_607;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0624)
                                                  0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_608 g) from (by
                                          unfold nb078_alpha_dummy_608;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0625 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠
        (nb078_alpha_dummy_581) from (by
          unfold nb078_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0621) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_582 g) from (by
          unfold nb078_alpha_dummy_582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0623 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0063 x y g)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_578) from
                                    (by
                                      unfold nb078_alpha_dummy_578;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0620)
                                              1)))) (show
                                    (nb078_alpha_dummy_573 g) ≠ (nb078_alpha_dummy_580 g) from
                                    (by
                                      unfold nb078_alpha_dummy_580;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0622 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_577) from (by
                                        unfold nb078_alpha_dummy_577;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0620)
                                                0)))) (show (nb078_alpha_dummy_573 g) ≠
                                        (nb078_alpha_dummy_579 g) from (by
                                        unfold nb078_alpha_dummy_579;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0622 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_607) from
                                        (by
                                          unfold nb078_alpha_dummy_607;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0624)
                                                  0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_608 g) from (by
                                          unfold nb078_alpha_dummy_608;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0625 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠
        (nb078_alpha_dummy_581) from (by
          unfold nb078_alpha_dummy_581;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0621) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_582 g) from (by
          unfold nb078_alpha_dummy_582;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0623 g) 0)))) (TAlphaVar.here _ _ _)))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb078_alpha_dummy_569))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_570))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
                                      ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0063 x y g)))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0064 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_571) ≠
        (nb078_alpha_dummy_614) from (by
          unfold nb078_alpha_dummy_614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 1)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_616 g) from (by
          unfold nb078_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_643) from (by
          unfold nb078_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0662) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_644 g) from (by
          unfold nb078_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0663 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_617) from (by
          unfold nb078_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0659) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_618 g) from (by
          unfold nb078_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0661 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0065 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614),
        (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
        ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617),
        (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_571) ≠
        (nb078_alpha_dummy_614) from (by
          unfold nb078_alpha_dummy_614;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 1)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_616 g) from (by
          unfold nb078_alpha_dummy_616;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_613) from (by
          unfold nb078_alpha_dummy_613;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0658) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_615 g) from (by
          unfold nb078_alpha_dummy_615;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0660 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_643) from (by
          unfold nb078_alpha_dummy_643;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0662) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_644 g) from (by
          unfold nb078_alpha_dummy_644;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0663 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_571) ≠ (nb078_alpha_dummy_617) from (by
          unfold nb078_alpha_dummy_617;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0659) 0)))) (show (nb078_alpha_dummy_574 g) ≠
        (nb078_alpha_dummy_618 g) from (by
          unfold nb078_alpha_dummy_618;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0661 g) 0)))) (TAlphaVar.here _ _ _)))))))
                                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_569))).fv ∪ ((Class.cv (nb078_alpha_dummy_571))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_572 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_574 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0065 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_645), (nb078_alpha_dummy_646 g)), ((nb078_alpha_dummy_614),
        (nb078_alpha_dummy_616 g)), ((nb078_alpha_dummy_613), (nb078_alpha_dummy_615 g)),
        ((nb078_alpha_dummy_643), (nb078_alpha_dummy_644 g)), ((nb078_alpha_dummy_617),
        (nb078_alpha_dummy_618 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cab (TAlphaWff.ex
                (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0074 x y g))))))
          (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0075 x y g)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠
        (nb078_alpha_dummy_728) from (by
          unfold nb078_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 1)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_730 g) from (by
          unfold nb078_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_757) from (by
          unfold nb078_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_758 g) from (by
          unfold nb078_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_731) from (by
          unfold nb078_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_732 g) from (by
          unfold nb078_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0076 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728),
        (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
        ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731),
        (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb078_alpha_dummy_570) ≠
        (nb078_alpha_dummy_728) from (by
          unfold nb078_alpha_dummy_728;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 1)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_730 g) from (by
          unfold nb078_alpha_dummy_730;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_727) from (by
          unfold nb078_alpha_dummy_727;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0788) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_729 g) from (by
          unfold nb078_alpha_dummy_729;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0790 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_757) from (by
          unfold nb078_alpha_dummy_757;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0792) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_758 g) from (by
          unfold nb078_alpha_dummy_758;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0793 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_570) ≠ (nb078_alpha_dummy_731) from (by
          unfold nb078_alpha_dummy_731;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0789) 0)))) (show (nb078_alpha_dummy_573 g) ≠
        (nb078_alpha_dummy_732 g) from (by
          unfold nb078_alpha_dummy_732;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0791 g) 0)))) (TAlphaVar.there (freshVar_injective
        (((syn_ccnv (Class.cv (nb078_alpha_dummy_001)))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv
        (nb078_alpha_dummy_001))))).fv) (by decide)) (freshVar_injective
        (((syn_ccnv (Class.cv g))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv g)))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                        (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_571))).fv ∪ ((Class.cv (nb078_alpha_dummy_570))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_574 g))).fv ∪
        ((Class.cv (nb078_alpha_dummy_573 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                    (TAlphaClass.cab (TAlphaWff.neg
                                        (TAlphaWff.conj (nb078_split_alpha_0076 x y g)
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_759), (nb078_alpha_dummy_760 g)), ((nb078_alpha_dummy_728),
        (nb078_alpha_dummy_730 g)), ((nb078_alpha_dummy_727), (nb078_alpha_dummy_729 g)),
        ((nb078_alpha_dummy_757), (nb078_alpha_dummy_758 g)), ((nb078_alpha_dummy_731),
        (nb078_alpha_dummy_732 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                                  (TAlphaWff.neg (nb078_split_alpha_0077 x y g)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0078 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0078 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_405), (nb078_alpha_dummy_406 g)), ((nb078_alpha_dummy_374),
        (nb078_alpha_dummy_376 g)), ((nb078_alpha_dummy_373), (nb078_alpha_dummy_375 g)),
        ((nb078_alpha_dummy_403), (nb078_alpha_dummy_404 g)), ((nb078_alpha_dummy_377),
        (nb078_alpha_dummy_378 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg (nb078_split_alpha_0079 x y g)))))
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0080 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
        (TAlphaWff.neg (TAlphaWff.neg (nb078_split_alpha_0080 x y g))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_441), (nb078_alpha_dummy_442 g)), ((nb078_alpha_dummy_410),
        (nb078_alpha_dummy_412 g)), ((nb078_alpha_dummy_409), (nb078_alpha_dummy_411 g)),
        ((nb078_alpha_dummy_439), (nb078_alpha_dummy_440 g)), ((nb078_alpha_dummy_413),
        (nb078_alpha_dummy_414 g)), ((nb078_alpha_dummy_368), (nb078_alpha_dummy_370 g)),
        ((nb078_alpha_dummy_367), (nb078_alpha_dummy_369 g)), ((nb078_alpha_dummy_371),
        (nb078_alpha_dummy_372 g)), ((nb078_alpha_dummy_571), (nb078_alpha_dummy_574 g)),
        ((nb078_alpha_dummy_570), (nb078_alpha_dummy_573 g)), ((nb078_alpha_dummy_569),
        (nb078_alpha_dummy_572 g)), ((nb078_alpha_dummy_575), (nb078_alpha_dummy_576 g)),
        ((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)), ((nb078_alpha_dummy_565),
        (nb078_alpha_dummy_566 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
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
                                (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_571) from (by
                                    unfold nb078_alpha_dummy_571;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0752) 2))))
                                (show g ≠ (nb078_alpha_dummy_574 g) from (by
                                    unfold nb078_alpha_dummy_574;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0754 g)
                                            2)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_570) from
                                    (by
                                      unfold nb078_alpha_dummy_570;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0752)
                                              1)))) (show g ≠ (nb078_alpha_dummy_573 g) from (by
                                      unfold nb078_alpha_dummy_573;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0754 g)
                                              1)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_569) from (by
                                        unfold nb078_alpha_dummy_569;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0752)
                                                0)))) (show g ≠ (nb078_alpha_dummy_572 g) from
                                      (by
                                        unfold nb078_alpha_dummy_572;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0754 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_575) from
                                        (by
                                          unfold nb078_alpha_dummy_575;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0753)
                                                  0)))) (show g ≠ (nb078_alpha_dummy_576 g) from
                                        (by
                                          unfold nb078_alpha_dummy_576;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0755 g) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_001) ≠
        (nb078_alpha_dummy_567) from (by
          unfold nb078_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0750) 0)))) (show g ≠ (nb078_alpha_dummy_568 g) from (by
          unfold nb078_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0751 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_001) ≠ (nb078_alpha_dummy_565) from (by
          unfold nb078_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0748) 0)))) (show g ≠ (nb078_alpha_dummy_566 g) from (by
          unfold nb078_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0749 g) 0)))) (TAlphaVar.here _ _ _)))))))))))))))))))))

theorem nb078_wpp_notmem_1930 : (nb078_alpha_dummy_567) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_567, fv_syn_cid] using (nb078_compact_fv_empty_0454)

theorem nb078_wpp_notmem_1931 (g : Var) : (nb078_alpha_dummy_568 g) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_568, fv_syn_cid] using (nb078_compact_fv_empty_0455 g)

theorem nb078_wpp_notmem_1932 : (nb078_alpha_dummy_565) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_565, fv_syn_cid] using (nb078_compact_fv_empty_0456)

theorem nb078_wpp_notmem_1933 (g : Var) : (nb078_alpha_dummy_566 g) ∉ ((syn_cid)).fv := by
  simpa only [nb078_alpha_dummy_566, fv_syn_cid] using (nb078_compact_fv_empty_0457 g)

theorem nb078_compact_envfresh_0273 (x : Var) (y : Var) (g : Var) :
    TEnvFresh
      [((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      ((syn_cid)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb078_alpha_dummy_567) (nb078_alpha_dummy_568 g)
      (nb078_wpp_notmem_1930) (nb078_wpp_notmem_1931 g)
      (TEnvFresh.consFresh (nb078_alpha_dummy_565) (nb078_alpha_dummy_566 g)
        (nb078_wpp_notmem_1932) (nb078_wpp_notmem_1933 g)
        (TEnvFresh.consFresh (nb078_alpha_dummy_001) g (nb078_wpp_notmem_1220)
          (nb078_wpp_notmem_1221 g)
          (TEnvFresh.consFresh (nb078_alpha_dummy_004) y (nb078_wpp_notmem_0512)
            (nb078_wpp_notmem_0513 y)
            (TEnvFresh.consFresh (nb078_alpha_dummy_003) x (nb078_wpp_notmem_0514)
              (nb078_wpp_notmem_0515 x) (TEnvFresh.nil ((syn_cid)).fv))))))

@[expose]
noncomputable def nb078_wpp_refl_0273 (x : Var) (y : Var) (g : Var) :
    TReflOn
      [((nb078_alpha_dummy_567), (nb078_alpha_dummy_568 g)),
        ((nb078_alpha_dummy_565), (nb078_alpha_dummy_566 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb078_compact_envfresh_0273 x y g)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
