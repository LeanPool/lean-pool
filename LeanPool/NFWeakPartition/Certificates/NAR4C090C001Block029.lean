/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block028

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part083`. -/


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
noncomputable def nb090_split_alpha_0061 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
        ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
        ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
        ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
        ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_499 A))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_468 A))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_499 A)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_500 h))
          (syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_470 h))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_500 h))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_501 A) from
                                (by
                                  unfold nb090_alpha_dummy_501;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0510 A) 0))))
                              (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_502 h) from
                                (by
                                  unfold nb090_alpha_dummy_502;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0511 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_499 A) from (by
                                    unfold nb090_alpha_dummy_499;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0508 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_500 h) from (by
                                    unfold nb090_alpha_dummy_500;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0509 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A),
        (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
        ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A),
        (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
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
        ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A),
        (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
        ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A),
        (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
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
                                    ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)),
                                    ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
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
                                    ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)),
                                    ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
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
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_501 A) from
                                (by
                                  unfold nb090_alpha_dummy_501;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0510 A) 0))))
                              (show (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_502 h) from
                                (by
                                  unfold nb090_alpha_dummy_502;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0511 h) 0))))
                              (TAlphaVar.there (show
                                  (nb090_alpha_dummy_468 A) ≠ (nb090_alpha_dummy_499 A) from (by
                                    unfold nb090_alpha_dummy_499;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0508 A)
                                            0)))) (show
                                  (nb090_alpha_dummy_470 h) ≠ (nb090_alpha_dummy_500 h) from (by
                                    unfold nb090_alpha_dummy_500;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb090_support_mem_0509 h)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A),
        (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
        ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A),
        (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
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
        ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)), ((nb090_alpha_dummy_499 A),
        (nb090_alpha_dummy_500 h)), ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
        ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)), ((nb090_alpha_dummy_497 A),
        (nb090_alpha_dummy_498 h)), ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
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
                                    ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)),
                                    ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
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
                                    ((nb090_alpha_dummy_501 A), (nb090_alpha_dummy_502 h)),
                                    ((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
                                    ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
                                    ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
                                    ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
                                    ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_499 A), (nb090_alpha_dummy_500 h)),
            ((nb090_alpha_dummy_468 A), (nb090_alpha_dummy_470 h)),
            ((nb090_alpha_dummy_467 A), (nb090_alpha_dummy_469 h)),
            ((nb090_alpha_dummy_497 A), (nb090_alpha_dummy_498 h)),
            ((nb090_alpha_dummy_471 A), (nb090_alpha_dummy_472 h)),
            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
            ((nb090_alpha_dummy_001 A), u),
            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part084`. -/


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
noncomputable def nb090_split_alpha_0062 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_515 A))
          (Class.cab (nb090_alpha_dummy_509 A)
            (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_515 A))
            (Class.cab (nb090_alpha_dummy_509 A)
              (syn_wrex (nb090_alpha_dummy_510 A) (Class.cv (nb090_alpha_dummy_503 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_509 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_516 h))
          (Class.cab (nb090_alpha_dummy_511 h)
            (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_516 h))
            (Class.cab (nb090_alpha_dummy_511 h)
              (syn_wrex (nb090_alpha_dummy_512 h) (Class.cv (nb090_alpha_dummy_505 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_511 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_512 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_510 A) from (by
                      unfold nb090_alpha_dummy_510;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
                  (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_512 h) from (by
                      unfold nb090_alpha_dummy_512;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_509 A) from (by
                        unfold nb090_alpha_dummy_509;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
                    (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_511 h) from (by
                        unfold nb090_alpha_dummy_511;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0518 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_515 A) from (by
                          unfold nb090_alpha_dummy_515;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0520 A) 0))))
                      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_516 h) from (by
                          unfold nb090_alpha_dummy_516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0521 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_513 A) from (by
                            unfold nb090_alpha_dummy_513;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0517 A) 0))))
                        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_514 h) from (by
                            unfold nb090_alpha_dummy_514;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0519 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv) (by decide))
                          (freshVar_injective (((syn_ccnv (Class.cv h))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_517 A) from (by
                              unfold nb090_alpha_dummy_517;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                          (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_519 h) from (by
                              unfold nb090_alpha_dummy_519;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_518 A) from (by
                                unfold nb090_alpha_dummy_518;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                            (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_520 h) from (by
                                unfold nb090_alpha_dummy_520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_524 A) from (by
          unfold nb090_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 1)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_527 h) from (by
          unfold nb090_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_523 A) from (by
          unfold nb090_alpha_dummy_523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 0)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_526 h) from (by
          unfold nb090_alpha_dummy_526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
          unfold nb090_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A)
                  0)))) (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
          unfold nb090_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A),
        (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A),
        (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A),
        (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A),
        (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A),
        (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A),
        (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_524
        A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525
        A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525
        A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                      (by
                                        unfold nb090_alpha_dummy_521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090_alpha_dummy_519 h) ≠
                                        (nb090_alpha_dummy_522 h) from (by
                                        unfold nb090_alpha_dummy_522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                                    ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                                    ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                                    ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                                    ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                                    ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
                                    ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                    (by
                                      unfold nb090_alpha_dummy_521;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0524 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from
                                    (by
                                      unfold nb090_alpha_dummy_522;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0525 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                      (by
                                        unfold nb090_alpha_dummy_521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090_alpha_dummy_519 h) ≠
                                        (nb090_alpha_dummy_522 h) from (by
                                        unfold nb090_alpha_dummy_522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                                    ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                                    ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                                    ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                                    ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                                    ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
                                    ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                                    ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                    ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                    ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                    ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_510 A) from (by
                        unfold nb090_alpha_dummy_510;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
                    (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_512 h) from (by
                        unfold nb090_alpha_dummy_512;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0518 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_509 A) from (by
                          unfold nb090_alpha_dummy_509;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
                      (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_511 h) from (by
                          unfold nb090_alpha_dummy_511;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_515 A) from (by
                            unfold nb090_alpha_dummy_515;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0520 A) 0))))
                        (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_516 h) from (by
                            unfold nb090_alpha_dummy_516;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0521 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_503 A) ≠ (nb090_alpha_dummy_513 A) from (by
                              unfold nb090_alpha_dummy_513;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0517 A) 0))))
                          (show (nb090_alpha_dummy_505 h) ≠ (nb090_alpha_dummy_514 h) from (by
                              unfold nb090_alpha_dummy_514;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0519 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((syn_ccnv (Class.cv (nb090_alpha_dummy_000 A)))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv h))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_503 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_504 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_505 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_506 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_517 A) from (by
                                unfold nb090_alpha_dummy_517;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                            (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_519 h) from (by
                                unfold nb090_alpha_dummy_519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_518 A) from
                                (by
                                  unfold nb090_alpha_dummy_518;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                              (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_520 h) from
                                (by
                                  unfold nb090_alpha_dummy_520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_510 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_512 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_524 A) from (by
          unfold nb090_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 1)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_527 h) from (by
          unfold nb090_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_523 A) from (by
          unfold nb090_alpha_dummy_523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A)
                  0)))) (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_526 h) from (by
          unfold nb090_alpha_dummy_526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_517 A) ≠
        (nb090_alpha_dummy_521 A) from (by
          unfold nb090_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A)
                  0)))) (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
          unfold nb090_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A),
        (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A),
        (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A),
        (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A),
        (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A),
        (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A),
        (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_524
        A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525
        A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525
        A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A)
                                        from (by
                                          unfold nb090_alpha_dummy_521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0524 A) 0)))) (show
                                        (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h)
                                        from (by
                                          unfold nb090_alpha_dummy_522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0525 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                                      ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                                      ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                                      ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                                      ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                                      ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
                                      ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                      (by
                                        unfold nb090_alpha_dummy_521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090_alpha_dummy_519 h) ≠
                                        (nb090_alpha_dummy_522 h) from (by
                                        unfold nb090_alpha_dummy_522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A)
                                        from (by
                                          unfold nb090_alpha_dummy_521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0524 A) 0)))) (show
                                        (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h)
                                        from (by
                                          unfold nb090_alpha_dummy_522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0525 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                                      ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                                      ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                                      ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                                      ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                                      ((nb090_alpha_dummy_515 A), (nb090_alpha_dummy_516 h)),
                                      ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                                      ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                      ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                      ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                      ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part085`. -/


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
noncomputable def nb090_split_alpha_0063 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
        ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
        ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
        ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_543 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_510 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_543 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_510 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_544 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_544 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_512 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_517 A) from (by
                      unfold nb090_alpha_dummy_517;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                  (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_519 h) from (by
                      unfold nb090_alpha_dummy_519;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_518 A) from (by
                        unfold nb090_alpha_dummy_518;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                    (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_520 h) from (by
                        unfold nb090_alpha_dummy_520;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0523 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_543 A) from (by
                          unfold nb090_alpha_dummy_543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0552 A) 0))))
                      (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_544 h) from (by
                          unfold nb090_alpha_dummy_544;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0553 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_541 A) from (by
                            unfold nb090_alpha_dummy_541;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0550 A) 0))))
                        (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_542 h) from (by
                            unfold nb090_alpha_dummy_542;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0551 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_524 A) from
                                      (by
                                        unfold nb090_alpha_dummy_524;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0526 A)
                                                1)))) (show (nb090_alpha_dummy_519 h) ≠
                                        (nb090_alpha_dummy_527 h) from (by
                                        unfold nb090_alpha_dummy_527;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0527 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_523 A)
                                        from (by
                                          unfold nb090_alpha_dummy_523;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0526 A) 0)))) (show
                                        (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_526 h)
                                        from (by
                                          unfold nb090_alpha_dummy_526;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0527 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_517 A) ≠
        (nb090_alpha_dummy_521 A) from (by
          unfold nb090_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A) 0)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_522 h) from (by
          unfold nb090_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_525 A),
        (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)),
                                        ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
                                        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                                        ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                                        ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                                        ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
                                        ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
                                        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                                        ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                                        ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
                                        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                                        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                                        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                                        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                                        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                                        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)),
        ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A),
        (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
        ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A),
        (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
        ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A),
        (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
        ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A),
        (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
                                unfold nb090_alpha_dummy_521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
                                unfold nb090_alpha_dummy_522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                            ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                            ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                            ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
                            ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
                            ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                            ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                            ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
                            ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                            ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                            ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                            ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
                              unfold nb090_alpha_dummy_521;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                          (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
                              unfold nb090_alpha_dummy_522;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
                                unfold nb090_alpha_dummy_521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
                                unfold nb090_alpha_dummy_522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                            ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                            ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                            ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
                            ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
                            ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                            ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                            ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
                            ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                            ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                            ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                            ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_517 A) from (by
                        unfold nb090_alpha_dummy_517;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                    (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_519 h) from (by
                        unfold nb090_alpha_dummy_519;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0523 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_518 A) from (by
                          unfold nb090_alpha_dummy_518;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                      (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_520 h) from (by
                          unfold nb090_alpha_dummy_520;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_543 A) from (by
                            unfold nb090_alpha_dummy_543;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0552 A) 0))))
                        (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_544 h) from (by
                            unfold nb090_alpha_dummy_544;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0553 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_510 A) ≠ (nb090_alpha_dummy_541 A) from (by
                              unfold nb090_alpha_dummy_541;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0550 A) 0))))
                          (show (nb090_alpha_dummy_512 h) ≠ (nb090_alpha_dummy_542 h) from (by
                              unfold nb090_alpha_dummy_542;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0551 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_510 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_512 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_517 A) ≠
        (nb090_alpha_dummy_524 A) from (by
                                          unfold nb090_alpha_dummy_524;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0526 A) 1)))) (show
                                        (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_527 h)
                                        from (by
                                          unfold nb090_alpha_dummy_527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0527 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_517 A) ≠
        (nb090_alpha_dummy_523 A) from (by
          unfold nb090_alpha_dummy_523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 0)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_526 h) from (by
          unfold nb090_alpha_dummy_526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
          unfold nb090_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A) 0)))) (show (nb090_alpha_dummy_519 h) ≠
        (nb090_alpha_dummy_522 h) from (by
          unfold nb090_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_525 A),
        (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A), (nb090_alpha_dummy_527 h)),
        ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)), ((nb090_alpha_dummy_521 A),
        (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
        ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)), ((nb090_alpha_dummy_543 A),
        (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
        ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)), ((nb090_alpha_dummy_509 A),
        (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
        ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_531 A) from (by
          unfold
            nb090_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_532 h) from (by
          unfold
            nb090_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_529 A) from (by
          unfold
            nb090_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_530 h) from (by
          unfold
            nb090_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_525 A), (nb090_alpha_dummy_528 h)), ((nb090_alpha_dummy_524 A),
        (nb090_alpha_dummy_527 h)), ((nb090_alpha_dummy_523 A), (nb090_alpha_dummy_526 h)),
        ((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)), ((nb090_alpha_dummy_517 A),
        (nb090_alpha_dummy_519 h)), ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
        ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)), ((nb090_alpha_dummy_541 A),
        (nb090_alpha_dummy_542 h)), ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
        ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)), ((nb090_alpha_dummy_539 A),
        (nb090_alpha_dummy_540 h)), ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠ (nb090_alpha_dummy_535 A) from (by
          unfold
            nb090_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_536 h) from (by
          unfold
            nb090_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_524 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090_alpha_dummy_527 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_517
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_519 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_525 A) ≠ (nb090_alpha_dummy_537 A) from (by
          unfold
            nb090_alpha_dummy_537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_538 h) from (by
          unfold
            nb090_alpha_dummy_538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_525 A) ≠
        (nb090_alpha_dummy_533 A) from (by
          unfold
            nb090_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090_alpha_dummy_528 h) ≠ (nb090_alpha_dummy_534 h) from (by
          unfold
            nb090_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                (by
                                  unfold nb090_alpha_dummy_521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                              (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from
                                (by
                                  unfold nb090_alpha_dummy_522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                              ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                              ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                              ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
                              ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
                              ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                              ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                              ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
                              ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                              ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                              ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                              ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from (by
                                unfold nb090_alpha_dummy_521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from (by
                                unfold nb090_alpha_dummy_522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_517 A) ≠ (nb090_alpha_dummy_521 A) from
                                (by
                                  unfold nb090_alpha_dummy_521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                              (show (nb090_alpha_dummy_519 h) ≠ (nb090_alpha_dummy_522 h) from
                                (by
                                  unfold nb090_alpha_dummy_522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_521 A), (nb090_alpha_dummy_522 h)),
                              ((nb090_alpha_dummy_517 A), (nb090_alpha_dummy_519 h)),
                              ((nb090_alpha_dummy_518 A), (nb090_alpha_dummy_520 h)),
                              ((nb090_alpha_dummy_543 A), (nb090_alpha_dummy_544 h)),
                              ((nb090_alpha_dummy_541 A), (nb090_alpha_dummy_542 h)),
                              ((nb090_alpha_dummy_510 A), (nb090_alpha_dummy_512 h)),
                              ((nb090_alpha_dummy_509 A), (nb090_alpha_dummy_511 h)),
                              ((nb090_alpha_dummy_539 A), (nb090_alpha_dummy_540 h)),
                              ((nb090_alpha_dummy_513 A), (nb090_alpha_dummy_514 h)),
                              ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                              ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                              ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
