/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C090C001Part060Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part060`. -/


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
noncomputable def nb090_split_alpha_0038 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_437 A))
          (Class.cab (nb090_alpha_dummy_431 A)
            (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_432 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_437 A))
            (Class.cab (nb090_alpha_dummy_431 A)
              (syn_wrex (nb090_alpha_dummy_432 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_431 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_438 h))
          (Class.cab (nb090_alpha_dummy_433 h)
            (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_438 h))
            (Class.cab (nb090_alpha_dummy_433 h)
              (syn_wrex (nb090_alpha_dummy_434 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_433 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_432 A) from (by
                      unfold nb090_alpha_dummy_432;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
                  (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_434 h) from (by
                      unfold nb090_alpha_dummy_434;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_431 A) from (by
                        unfold nb090_alpha_dummy_431;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
                    (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_433 h) from (by
                        unfold nb090_alpha_dummy_433;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0438 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_437 A) from (by
                          unfold nb090_alpha_dummy_437;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0440 A) 0))))
                      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_438 h) from (by
                          unfold nb090_alpha_dummy_438;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0441 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_435 A) from (by
                            unfold nb090_alpha_dummy_435;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0437 A) 0))))
                        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_436 h) from (by
                            unfold nb090_alpha_dummy_436;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0439 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_439 A) from (by
                              unfold nb090_alpha_dummy_439;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                          (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_441 h) from (by
                              unfold nb090_alpha_dummy_441;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_440 A) from (by
                                unfold nb090_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                            (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_442 h) from (by
                                unfold nb090_alpha_dummy_442;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_446 A) from (by
          unfold nb090_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_449 h) from (by
          unfold nb090_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_445 A) from (by
          unfold nb090_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_448 h) from (by
          unfold nb090_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from (by
          unfold nb090_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A)
                  0)))) (show (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from (by
          unfold nb090_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A),
        (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_446
        A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A),
        (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                      (by
                                        unfold nb090_alpha_dummy_443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090_alpha_dummy_441 h) ≠
                                        (nb090_alpha_dummy_444 h) from (by
                                        unfold nb090_alpha_dummy_444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                    ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                    ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                    ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                    ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                    ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
                                    ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                    (by
                                      unfold nb090_alpha_dummy_443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from
                                    (by
                                      unfold nb090_alpha_dummy_444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                      (by
                                        unfold nb090_alpha_dummy_443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090_alpha_dummy_441 h) ≠
                                        (nb090_alpha_dummy_444 h) from (by
                                        unfold nb090_alpha_dummy_444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                    ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                    ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                    ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                    ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                    ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
                                    ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_432 A) from (by
                        unfold nb090_alpha_dummy_432;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
                    (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_434 h) from (by
                        unfold nb090_alpha_dummy_434;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0438 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_431 A) from (by
                          unfold nb090_alpha_dummy_431;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
                      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_433 h) from (by
                          unfold nb090_alpha_dummy_433;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_437 A) from (by
                            unfold nb090_alpha_dummy_437;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0440 A) 0))))
                        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_438 h) from (by
                            unfold nb090_alpha_dummy_438;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0441 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_435 A) from (by
                              unfold nb090_alpha_dummy_435;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0437 A) 0))))
                          (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_436 h) from (by
                              unfold nb090_alpha_dummy_436;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0439 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_424 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_427 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_439 A) from (by
                                unfold nb090_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                            (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_441 h) from (by
                                unfold nb090_alpha_dummy_441;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_440 A) from
                                (by
                                  unfold nb090_alpha_dummy_440;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                              (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_442 h) from
                                (by
                                  unfold nb090_alpha_dummy_442;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_432 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_434 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_446 A) from (by
          unfold nb090_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_449 h) from (by
          unfold nb090_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_445 A) from (by
          unfold nb090_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A)
                  0)))) (show (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_448 h) from (by
          unfold nb090_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_439 A) ≠
        (nb090_alpha_dummy_443 A) from (by
          unfold nb090_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A)
                  0)))) (show (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from (by
          unfold nb090_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A),
        (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_446
        A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)), ((nb090_alpha_dummy_431 A),
        (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A)
                                        from (by
                                          unfold nb090_alpha_dummy_443;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0444 A) 0)))) (show
                                        (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h)
                                        from (by
                                          unfold nb090_alpha_dummy_444;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0445 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                      ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                      ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                      ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                      ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                      ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
                                      ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                      (by
                                        unfold nb090_alpha_dummy_443;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0444 A)
                                                0)))) (show (nb090_alpha_dummy_441 h) ≠
                                        (nb090_alpha_dummy_444 h) from (by
                                        unfold nb090_alpha_dummy_444;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0445 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A)
                                        from (by
                                          unfold nb090_alpha_dummy_443;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0444 A) 0)))) (show
                                        (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h)
                                        from (by
                                          unfold nb090_alpha_dummy_444;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0445 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                      ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                      ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                      ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                      ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                      ((nb090_alpha_dummy_437 A), (nb090_alpha_dummy_438 h)),
                                      ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part061`. -/


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
noncomputable def nb090_split_alpha_0039 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)),
        ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
        ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)),
        ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.classMem (Class.cv (nb090_alpha_dummy_463 A))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_432 A)))))
      (Wff.classMem (Class.cv (nb090_alpha_dummy_464 h))
        (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_434 h))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_439 A) from (by
                            unfold nb090_alpha_dummy_439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                        (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_441 h) from (by
                            unfold nb090_alpha_dummy_441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_440 A) from (by
                              unfold nb090_alpha_dummy_440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                          (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_442 h) from (by
                              unfold nb090_alpha_dummy_442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_465 A) from (by
                                unfold nb090_alpha_dummy_465;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0472 A) 0))))
                            (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_466 h) from (by
                                unfold nb090_alpha_dummy_466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0473 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_463 A) from
                                (by
                                  unfold nb090_alpha_dummy_463;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0470 A) 0))))
                              (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_464 h) from
                                (by
                                  unfold nb090_alpha_dummy_464;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0471 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_439 A) ≠
        (nb090_alpha_dummy_446 A) from (by
          unfold nb090_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_449 h) from (by
          unfold nb090_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_445 A) from (by
          unfold nb090_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_448 h) from (by
          unfold nb090_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from (by
          unfold nb090_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A) 0)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_444 h) from (by
          unfold nb090_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_446
        A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                    (by
                                      unfold nb090_alpha_dummy_443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from
                                    (by
                                      unfold nb090_alpha_dummy_444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                  ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                  ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                  ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)),
                                  ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)),
                                  ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                  ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                  ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)),
                                  ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                  ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                  ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                  ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                  ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                  ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from (by
                                    unfold nb090_alpha_dummy_443;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0444 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from (by
                                    unfold nb090_alpha_dummy_444;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0445 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                    (by
                                      unfold nb090_alpha_dummy_443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from
                                    (by
                                      unfold nb090_alpha_dummy_444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                  ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                  ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                  ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)),
                                  ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)),
                                  ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                  ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                  ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)),
                                  ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                  ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                  ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                  ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                  ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                  ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_439 A) from (by
                            unfold nb090_alpha_dummy_439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0442 A) 0))))
                        (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_441 h) from (by
                            unfold nb090_alpha_dummy_441;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0443 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_440 A) from (by
                              unfold nb090_alpha_dummy_440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0442 A) 1))))
                          (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_442 h) from (by
                              unfold nb090_alpha_dummy_442;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0443 h) 1))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_465 A) from (by
                                unfold nb090_alpha_dummy_465;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0472 A) 0))))
                            (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_466 h) from (by
                                unfold nb090_alpha_dummy_466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0473 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_432 A) ≠ (nb090_alpha_dummy_463 A) from
                                (by
                                  unfold nb090_alpha_dummy_463;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0470 A) 0))))
                              (show (nb090_alpha_dummy_434 h) ≠ (nb090_alpha_dummy_464 h) from
                                (by
                                  unfold nb090_alpha_dummy_464;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0471 h) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_432 A))).fv)
                          (by decide))
                        (freshVar_injective (((Class.cv (nb090_alpha_dummy_434 h))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb090_alpha_dummy_439 A) ≠
        (nb090_alpha_dummy_446 A) from (by
          unfold nb090_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 1)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_449 h) from (by
          unfold nb090_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_445 A) from (by
          unfold nb090_alpha_dummy_445;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0446 A) 0)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_448 h) from (by
          unfold nb090_alpha_dummy_448;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0447 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from (by
          unfold nb090_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0444 A) 0)))) (show (nb090_alpha_dummy_441 h) ≠
        (nb090_alpha_dummy_444 h) from (by
          unfold nb090_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0445 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0450
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0451
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0448
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0449
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠ (nb090_alpha_dummy_453 A) from (by
          unfold
            nb090_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0454
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_454 h) from (by
          unfold
            nb090_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0455
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_451 A) from (by
          unfold
            nb090_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0452
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_452 h) from (by
          unfold
            nb090_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0453
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_447 A), (nb090_alpha_dummy_450 h)), ((nb090_alpha_dummy_446 A),
        (nb090_alpha_dummy_449 h)), ((nb090_alpha_dummy_445 A), (nb090_alpha_dummy_448 h)),
        ((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)), ((nb090_alpha_dummy_439 A),
        (nb090_alpha_dummy_441 h)), ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
        ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)), ((nb090_alpha_dummy_463 A),
        (nb090_alpha_dummy_464 h)), ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
        ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)), ((nb090_alpha_dummy_461 A),
        (nb090_alpha_dummy_462 h)), ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_439 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_441 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_446
        A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠ (nb090_alpha_dummy_457 A) from (by
          unfold
            nb090_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0458
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_458 h) from (by
          unfold
            nb090_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0459
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_446 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0456
                    A)
                  0)))) (show (nb090_alpha_dummy_449 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0457
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_439
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_441 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_447
        A) ≠ (nb090_alpha_dummy_459 A) from (by
          unfold
            nb090_alpha_dummy_459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0462
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_460 h) from (by
          unfold
            nb090_alpha_dummy_460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0463
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_447 A) ≠
        (nb090_alpha_dummy_455 A) from (by
          unfold
            nb090_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0460
                    A)
                  0)))) (show (nb090_alpha_dummy_450 h) ≠ (nb090_alpha_dummy_456 h) from (by
          unfold
            nb090_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0461
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                    (by
                                      unfold nb090_alpha_dummy_443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from
                                    (by
                                      unfold nb090_alpha_dummy_444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                  ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                  ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                  ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)),
                                  ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)),
                                  ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                  ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                  ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)),
                                  ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                  ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                  ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                  ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                  ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                  ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from (by
                                    unfold nb090_alpha_dummy_443;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0444 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from (by
                                    unfold nb090_alpha_dummy_444;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0445 h)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_439 A) ≠ (nb090_alpha_dummy_443 A) from
                                    (by
                                      unfold nb090_alpha_dummy_443;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0444 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_441 h) ≠ (nb090_alpha_dummy_444 h) from
                                    (by
                                      unfold nb090_alpha_dummy_444;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0445 h)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.refl_of_closed
                                [((nb090_alpha_dummy_443 A), (nb090_alpha_dummy_444 h)),
                                  ((nb090_alpha_dummy_439 A), (nb090_alpha_dummy_441 h)),
                                  ((nb090_alpha_dummy_440 A), (nb090_alpha_dummy_442 h)),
                                  ((nb090_alpha_dummy_465 A), (nb090_alpha_dummy_466 h)),
                                  ((nb090_alpha_dummy_463 A), (nb090_alpha_dummy_464 h)),
                                  ((nb090_alpha_dummy_432 A), (nb090_alpha_dummy_434 h)),
                                  ((nb090_alpha_dummy_431 A), (nb090_alpha_dummy_433 h)),
                                  ((nb090_alpha_dummy_461 A), (nb090_alpha_dummy_462 h)),
                                  ((nb090_alpha_dummy_435 A), (nb090_alpha_dummy_436 h)),
                                  ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                  ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                  ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                  ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                  ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                  ((nb090_alpha_dummy_000 A), h),
                                  ((nb090_alpha_dummy_002 A), v),
                                  ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                    (nb090_alpha_dummy_004 v u A h))]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part062`. -/


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
noncomputable def nb090_split_alpha_0040 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_473 A))
          (Class.cab (nb090_alpha_dummy_467 A)
            (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_473 A))
            (Class.cab (nb090_alpha_dummy_467 A)
              (syn_wrex (nb090_alpha_dummy_468 A) (Class.cv (nb090_alpha_dummy_423 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_467 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_468 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_474 h))
          (Class.cab (nb090_alpha_dummy_469 h)
            (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_474 h))
            (Class.cab (nb090_alpha_dummy_469 h)
              (syn_wrex (nb090_alpha_dummy_470 h) (Class.cv (nb090_alpha_dummy_426 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_469 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_468 A) from (by
                      unfold nb090_alpha_dummy_468;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
                  (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_470 h) from (by
                      unfold nb090_alpha_dummy_470;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_467 A) from (by
                        unfold nb090_alpha_dummy_467;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
                    (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_469 h) from (by
                        unfold nb090_alpha_dummy_469;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0476 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_473 A) from (by
                          unfold nb090_alpha_dummy_473;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0478 A) 0))))
                      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_474 h) from (by
                          unfold nb090_alpha_dummy_474;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0479 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_471 A) from (by
                            unfold nb090_alpha_dummy_471;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0475 A) 0))))
                        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_472 h) from (by
                            unfold nb090_alpha_dummy_472;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0477 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv
                                  (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_425 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_428 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_475 A) from (by
                              unfold nb090_alpha_dummy_475;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                          (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_477 h) from (by
                              unfold nb090_alpha_dummy_477;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0481 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_476 A) from (by
                                unfold nb090_alpha_dummy_476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                            (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_478 h) from (by
                                unfold nb090_alpha_dummy_478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0481 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_468 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_470 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_482 A) from (by
          unfold nb090_alpha_dummy_482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 1)))) (show (nb090_alpha_dummy_477 h) ≠
        (nb090_alpha_dummy_485 h) from (by
          unfold nb090_alpha_dummy_485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_481 A) from (by
          unfold nb090_alpha_dummy_481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 0)))) (show (nb090_alpha_dummy_477 h) ≠
        (nb090_alpha_dummy_484 h) from (by
          unfold nb090_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A) from (by
          unfold nb090_alpha_dummy_479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A)
                  0)))) (show (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_480 h) from (by
          unfold nb090_alpha_dummy_480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A),
        (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)),
        ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A),
        (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
        ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A),
        (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A),
        (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)),
        ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A),
        (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
        ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A),
        (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_482
        A) ≠ (nb090_alpha_dummy_493 A) from (by
          unfold
            nb090_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_494 h) from (by
          unfold
            nb090_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_493 A) from (by
          unfold
            nb090_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_494 h) from (by
          unfold
            nb090_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_483
        A) ≠ (nb090_alpha_dummy_495 A) from (by
          unfold
            nb090_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_496 h) from (by
          unfold
            nb090_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_483
        A) ≠ (nb090_alpha_dummy_495 A) from (by
          unfold
            nb090_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_496 h) from (by
          unfold
            nb090_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A) from
                                      (by
                                        unfold nb090_alpha_dummy_479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090_alpha_dummy_477 h) ≠
                                        (nb090_alpha_dummy_480 h) from (by
                                        unfold nb090_alpha_dummy_480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)),
                                    ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)),
                                    ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A) from
                                    (by
                                      unfold nb090_alpha_dummy_479;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0482 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_480 h) from
                                    (by
                                      unfold nb090_alpha_dummy_480;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0483 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A) from
                                      (by
                                        unfold nb090_alpha_dummy_479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090_alpha_dummy_477 h) ≠
                                        (nb090_alpha_dummy_480 h) from (by
                                        unfold nb090_alpha_dummy_480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)),
                                    ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)),
                                    ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                    ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_468 A) from (by
                        unfold nb090_alpha_dummy_468;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
                    (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_470 h) from (by
                        unfold nb090_alpha_dummy_470;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0476 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_467 A) from (by
                          unfold nb090_alpha_dummy_467;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
                      (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_469 h) from (by
                          unfold nb090_alpha_dummy_469;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_473 A) from (by
                            unfold nb090_alpha_dummy_473;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0478 A) 0))))
                        (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_474 h) from (by
                            unfold nb090_alpha_dummy_474;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0479 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_423 A) ≠ (nb090_alpha_dummy_471 A) from (by
                              unfold nb090_alpha_dummy_471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0475 A) 0))))
                          (show (nb090_alpha_dummy_426 h) ≠ (nb090_alpha_dummy_472 h) from (by
                              unfold nb090_alpha_dummy_472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0477 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪ ((syn_ccnv
                                    (syn_ccnv (Class.cv (nb090_alpha_dummy_000 A))))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective
                                (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv ∪
                                  ((syn_ccnv (syn_ccnv
                                        (Class.cv (nb090_alpha_dummy_000 A))))).fv) (by decide))
                              (freshVar_injective (((syn_ccnv (Class.cv h))).fv ∪
                                  ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_423 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_425 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_426 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_428 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_475 A) from (by
                                unfold nb090_alpha_dummy_475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                            (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_477 h) from (by
                                unfold nb090_alpha_dummy_477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0481 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_476 A) from
                                (by
                                  unfold nb090_alpha_dummy_476;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                              (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_478 h) from
                                (by
                                  unfold nb090_alpha_dummy_478;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0481 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_468 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_470 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_482 A) from (by
          unfold nb090_alpha_dummy_482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 1)))) (show (nb090_alpha_dummy_477 h) ≠
        (nb090_alpha_dummy_485 h) from (by
          unfold nb090_alpha_dummy_485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_481 A) from (by
          unfold nb090_alpha_dummy_481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A)
                  0)))) (show (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_484 h) from (by
          unfold nb090_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_475 A) ≠
        (nb090_alpha_dummy_479 A) from (by
          unfold nb090_alpha_dummy_479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A)
                  0)))) (show (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_480 h) from (by
          unfold nb090_alpha_dummy_480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A),
        (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)),
        ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A),
        (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
        ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A),
        (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠ (nb090_alpha_dummy_489 A) from (by
          unfold
            nb090_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_490 h) from (by
          unfold
            nb090_alpha_dummy_490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_487 A) from (by
          unfold
            nb090_alpha_dummy_487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_488 h) from (by
          unfold
            nb090_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_483 A), (nb090_alpha_dummy_486 h)), ((nb090_alpha_dummy_482 A),
        (nb090_alpha_dummy_485 h)), ((nb090_alpha_dummy_481 A), (nb090_alpha_dummy_484 h)),
        ((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)), ((nb090_alpha_dummy_475 A),
        (nb090_alpha_dummy_477 h)), ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
        ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)), ((nb090_alpha_dummy_467 A),
        (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_477
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_475 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_482
        A) ≠ (nb090_alpha_dummy_493 A) from (by
          unfold
            nb090_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_494 h) from (by
          unfold
            nb090_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠ (nb090_alpha_dummy_493 A) from (by
          unfold
            nb090_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_494 h) from (by
          unfold
            nb090_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_482 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090_alpha_dummy_485 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_475
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_477 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_483
        A) ≠ (nb090_alpha_dummy_495 A) from (by
          unfold
            nb090_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_496 h) from (by
          unfold
            nb090_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_483
        A) ≠ (nb090_alpha_dummy_495 A) from (by
          unfold
            nb090_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_496 h) from (by
          unfold
            nb090_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_483 A) ≠
        (nb090_alpha_dummy_491 A) from (by
          unfold
            nb090_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090_alpha_dummy_486 h) ≠ (nb090_alpha_dummy_492 h) from (by
          unfold
            nb090_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A)
                                        from (by
                                          unfold nb090_alpha_dummy_479;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0482 A) 0)))) (show
                                        (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_480 h)
                                        from (by
                                          unfold nb090_alpha_dummy_480;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0483 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)),
                                      ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)),
                                      ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
                                      ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                      ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                      ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
                                      ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A) from
                                      (by
                                        unfold nb090_alpha_dummy_479;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0482 A)
                                                0)))) (show (nb090_alpha_dummy_477 h) ≠
                                        (nb090_alpha_dummy_480 h) from (by
                                        unfold nb090_alpha_dummy_480;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0483 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_475 A) ≠ (nb090_alpha_dummy_479 A)
                                        from (by
                                          unfold nb090_alpha_dummy_479;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0482 A) 0)))) (show
                                        (nb090_alpha_dummy_477 h) ≠ (nb090_alpha_dummy_480 h)
                                        from (by
                                          unfold nb090_alpha_dummy_480;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0483 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_479 A), (nb090_alpha_dummy_480 h)),
                                      ((nb090_alpha_dummy_475 A), (nb090_alpha_dummy_477 h)),
                                      ((nb090_alpha_dummy_476 A), (nb090_alpha_dummy_478 h)),
                                      ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                      ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                      ((nb090_alpha_dummy_473 A), (nb090_alpha_dummy_474 h)),
                                      ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                                      ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
