/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part029

/-! NF weak partition development: NAR4H5C095M3Part030. -/


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
noncomputable def nb095_split_alpha_0061 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_477 D R S_cls E), (nb095_alpha_dummy_478 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_477 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_477 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_471 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_472 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_471 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_478 f))
          (Class.cab (nb095_alpha_dummy_473 f)
            (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_478 f))
            (Class.cab (nb095_alpha_dummy_473 f)
              (syn_wrex (nb095_alpha_dummy_474 f) (Class.cv (nb095_alpha_dummy_467 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_473 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_474 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                      (nb095_alpha_dummy_472 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_472;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_474 f) from (by
                      unfold nb095_alpha_dummy_474;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                        (nb095_alpha_dummy_471 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_471;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_473 f) from (by
                        unfold nb095_alpha_dummy_473;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0476 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                          (nb095_alpha_dummy_477 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_477;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0478 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_478 f) from (by
                          unfold nb095_alpha_dummy_478;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0479 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                            (nb095_alpha_dummy_475 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_475;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0475 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_476 f) from (by
                            unfold nb095_alpha_dummy_476;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0477 f) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
                            (by decide))
                          (freshVar_injective (((syn_ccnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_468 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                              (nb095_alpha_dummy_479 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_479;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_481 f) from (by
                              unfold nb095_alpha_dummy_481;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                                (nb095_alpha_dummy_480 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0480 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_482 f) from (by
                                unfold nb095_alpha_dummy_482;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_474 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_486 D R S_cls E) from (by
          unfold nb095_alpha_dummy_486;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_489 f) from (by
          unfold nb095_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_485 D R S_cls E) from (by
          unfold nb095_alpha_dummy_485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_488 f) from (by
          unfold nb095_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_483 D R S_cls E) from (by
          unfold nb095_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
          unfold nb095_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_487 D R S_cls E), (nb095_alpha_dummy_490 f)),
        ((nb095_alpha_dummy_486 D R S_cls E), (nb095_alpha_dummy_489 f)),
        ((nb095_alpha_dummy_485 D R S_cls E), (nb095_alpha_dummy_488 f)),
        ((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
        ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
        ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_477 D R S_cls E), (nb095_alpha_dummy_478 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_486
        D R S_cls E) ≠ (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_487 D R S_cls E), (nb095_alpha_dummy_490 f)),
        ((nb095_alpha_dummy_486 D R S_cls E), (nb095_alpha_dummy_489 f)),
        ((nb095_alpha_dummy_485 D R S_cls E), (nb095_alpha_dummy_488 f)),
        ((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
        ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
        ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_477 D R S_cls E), (nb095_alpha_dummy_478 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487
        D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487
        D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_479 D R S_cls E) ≠
                                        (nb095_alpha_dummy_483 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                      (by
                                        unfold nb095_alpha_dummy_484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_483 D R S_cls E),
                                      (nb095_alpha_dummy_484 f)),
                                    ((nb095_alpha_dummy_479 D R S_cls E),
                                      (nb095_alpha_dummy_481 f)),
                                    ((nb095_alpha_dummy_480 D R S_cls E),
                                      (nb095_alpha_dummy_482 f)),
                                    ((nb095_alpha_dummy_472 D R S_cls E),
                                      (nb095_alpha_dummy_474 f)),
                                    ((nb095_alpha_dummy_471 D R S_cls E),
                                      (nb095_alpha_dummy_473 f)),
                                    ((nb095_alpha_dummy_477 D R S_cls E),
                                      (nb095_alpha_dummy_478 f)),
                                    ((nb095_alpha_dummy_475 D R S_cls E),
                                      (nb095_alpha_dummy_476 f)),
                                    ((nb095_alpha_dummy_466 D R S_cls E),
                                      (nb095_alpha_dummy_468 f)),
                                    ((nb095_alpha_dummy_465 D R S_cls E),
                                      (nb095_alpha_dummy_467 f)),
                                    ((nb095_alpha_dummy_469 D R S_cls E),
                                      (nb095_alpha_dummy_470 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_479 D R S_cls E) ≠
                                      (nb095_alpha_dummy_483 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_483;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                    (by
                                      unfold nb095_alpha_dummy_484;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0483 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_479 D R S_cls E) ≠
                                        (nb095_alpha_dummy_483 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                      (by
                                        unfold nb095_alpha_dummy_484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_483 D R S_cls E),
                                      (nb095_alpha_dummy_484 f)),
                                    ((nb095_alpha_dummy_479 D R S_cls E),
                                      (nb095_alpha_dummy_481 f)),
                                    ((nb095_alpha_dummy_480 D R S_cls E),
                                      (nb095_alpha_dummy_482 f)),
                                    ((nb095_alpha_dummy_472 D R S_cls E),
                                      (nb095_alpha_dummy_474 f)),
                                    ((nb095_alpha_dummy_471 D R S_cls E),
                                      (nb095_alpha_dummy_473 f)),
                                    ((nb095_alpha_dummy_477 D R S_cls E),
                                      (nb095_alpha_dummy_478 f)),
                                    ((nb095_alpha_dummy_475 D R S_cls E),
                                      (nb095_alpha_dummy_476 f)),
                                    ((nb095_alpha_dummy_466 D R S_cls E),
                                      (nb095_alpha_dummy_468 f)),
                                    ((nb095_alpha_dummy_465 D R S_cls E),
                                      (nb095_alpha_dummy_467 f)),
                                    ((nb095_alpha_dummy_469 D R S_cls E),
                                      (nb095_alpha_dummy_470 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                        (nb095_alpha_dummy_472 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_472;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_474 f) from (by
                        unfold nb095_alpha_dummy_474;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0476 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                          (nb095_alpha_dummy_471 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_471;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_473 f) from (by
                          unfold nb095_alpha_dummy_473;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                            (nb095_alpha_dummy_477 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_477;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0478 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_478 f) from (by
                            unfold nb095_alpha_dummy_478;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0479 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_465 D R S_cls E) ≠
                              (nb095_alpha_dummy_475 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_475;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0475 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_467 f) ≠ (nb095_alpha_dummy_476 f) from (by
                              unfold nb095_alpha_dummy_476;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0477 f) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                  (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective (((syn_ccnv (Class.cv f))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_467 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_468 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_472 D R S_cls E) ≠
                                (nb095_alpha_dummy_479 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0480 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_481 f) from (by
                                unfold nb095_alpha_dummy_481;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                                  (nb095_alpha_dummy_480 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_480;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0480 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_482 f) from
                                (by
                                  unfold nb095_alpha_dummy_482;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_474 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_486 D R S_cls E) from (by
          unfold nb095_alpha_dummy_486;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_489 f) from (by
          unfold nb095_alpha_dummy_489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_485 D R S_cls E) from (by
          unfold nb095_alpha_dummy_485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_488 f) from (by
          unfold nb095_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_483 D R S_cls E) from (by
          unfold nb095_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
          unfold nb095_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_487 D R S_cls E), (nb095_alpha_dummy_490 f)),
        ((nb095_alpha_dummy_486 D R S_cls E), (nb095_alpha_dummy_489 f)),
        ((nb095_alpha_dummy_485 D R S_cls E), (nb095_alpha_dummy_488 f)),
        ((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
        ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
        ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_477 D R S_cls E), (nb095_alpha_dummy_478 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_486
        D R S_cls E) ≠ (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_487 D R S_cls E), (nb095_alpha_dummy_490 f)),
        ((nb095_alpha_dummy_486 D R S_cls E), (nb095_alpha_dummy_489 f)),
        ((nb095_alpha_dummy_485 D R S_cls E), (nb095_alpha_dummy_488 f)),
        ((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
        ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
        ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_477 D R S_cls E), (nb095_alpha_dummy_478 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487
        D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487
        D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_483 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0482 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_481 f) ≠
        (nb095_alpha_dummy_484 f) from (by
                                          unfold nb095_alpha_dummy_484;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0483 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_483 D R S_cls E),
                                        (nb095_alpha_dummy_484 f)),
                                      ((nb095_alpha_dummy_479 D R S_cls E),
                                        (nb095_alpha_dummy_481 f)),
                                      ((nb095_alpha_dummy_480 D R S_cls E),
                                        (nb095_alpha_dummy_482 f)),
                                      ((nb095_alpha_dummy_472 D R S_cls E),
                                        (nb095_alpha_dummy_474 f)),
                                      ((nb095_alpha_dummy_471 D R S_cls E),
                                        (nb095_alpha_dummy_473 f)),
                                      ((nb095_alpha_dummy_477 D R S_cls E),
                                        (nb095_alpha_dummy_478 f)),
                                      ((nb095_alpha_dummy_475 D R S_cls E),
                                        (nb095_alpha_dummy_476 f)),
                                      ((nb095_alpha_dummy_466 D R S_cls E),
                                        (nb095_alpha_dummy_468 f)),
                                      ((nb095_alpha_dummy_465 D R S_cls E),
                                        (nb095_alpha_dummy_467 f)),
                                      ((nb095_alpha_dummy_469 D R S_cls E),
                                        (nb095_alpha_dummy_470 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_479 D R S_cls E) ≠
                                        (nb095_alpha_dummy_483 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                      (by
                                        unfold nb095_alpha_dummy_484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_483 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0482 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_481 f) ≠
        (nb095_alpha_dummy_484 f) from (by
                                          unfold nb095_alpha_dummy_484;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0483 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_483 D R S_cls E),
                                        (nb095_alpha_dummy_484 f)),
                                      ((nb095_alpha_dummy_479 D R S_cls E),
                                        (nb095_alpha_dummy_481 f)),
                                      ((nb095_alpha_dummy_480 D R S_cls E),
                                        (nb095_alpha_dummy_482 f)),
                                      ((nb095_alpha_dummy_472 D R S_cls E),
                                        (nb095_alpha_dummy_474 f)),
                                      ((nb095_alpha_dummy_471 D R S_cls E),
                                        (nb095_alpha_dummy_473 f)),
                                      ((nb095_alpha_dummy_477 D R S_cls E),
                                        (nb095_alpha_dummy_478 f)),
                                      ((nb095_alpha_dummy_475 D R S_cls E),
                                        (nb095_alpha_dummy_476 f)),
                                      ((nb095_alpha_dummy_466 D R S_cls E),
                                        (nb095_alpha_dummy_468 f)),
                                      ((nb095_alpha_dummy_465 D R S_cls E),
                                        (nb095_alpha_dummy_467 f)),
                                      ((nb095_alpha_dummy_469 D R S_cls E),
                                        (nb095_alpha_dummy_470 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0062 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
        ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_505 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_505 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_472 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_506 f))
          (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_506 f))
            (syn_cphi (Class.cv (nb095_alpha_dummy_474 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                      (nb095_alpha_dummy_479 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_479;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_481 f) from (by
                      unfold nb095_alpha_dummy_481;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                        (nb095_alpha_dummy_480 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_480;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_482 f) from (by
                        unfold nb095_alpha_dummy_482;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0481 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                          (nb095_alpha_dummy_505 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_505;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0510 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_506 f) from (by
                          unfold nb095_alpha_dummy_506;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0511 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                            (nb095_alpha_dummy_503 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_503;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0508 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_504 f) from (by
                            unfold nb095_alpha_dummy_504;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0509 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_474 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_479 D R S_cls E) ≠
                                        (nb095_alpha_dummy_486 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0484 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_489 f) from
                                      (by
                                        unfold nb095_alpha_dummy_489;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0485 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_485 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0484 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_481 f) ≠
        (nb095_alpha_dummy_488 f) from (by
                                          unfold nb095_alpha_dummy_488;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0485 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_483 D R S_cls E) from (by
          unfold nb095_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
          unfold nb095_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_487 D R S_cls E),
        (nb095_alpha_dummy_490 f)), ((nb095_alpha_dummy_486 D R S_cls E),
        (nb095_alpha_dummy_489 f)), ((nb095_alpha_dummy_485 D R S_cls E),
        (nb095_alpha_dummy_488 f)), ((nb095_alpha_dummy_483 D R S_cls E),
        (nb095_alpha_dummy_484 f)), ((nb095_alpha_dummy_479 D R S_cls E),
        (nb095_alpha_dummy_481 f)), ((nb095_alpha_dummy_480 D R S_cls E),
        (nb095_alpha_dummy_482 f)), ((nb095_alpha_dummy_505 D R S_cls E),
        (nb095_alpha_dummy_506 f)), ((nb095_alpha_dummy_503 D R S_cls E),
        (nb095_alpha_dummy_504 f)), ((nb095_alpha_dummy_472 D R S_cls E),
        (nb095_alpha_dummy_474 f)), ((nb095_alpha_dummy_471 D R S_cls E),
        (nb095_alpha_dummy_473 f)), ((nb095_alpha_dummy_501 D R S_cls E),
        (nb095_alpha_dummy_502 f)), ((nb095_alpha_dummy_475 D R S_cls E),
        (nb095_alpha_dummy_476 f)), ((nb095_alpha_dummy_466 D R S_cls E),
        (nb095_alpha_dummy_468 f)), ((nb095_alpha_dummy_465 D R S_cls E),
        (nb095_alpha_dummy_467 f)), ((nb095_alpha_dummy_469 D R S_cls E),
        (nb095_alpha_dummy_470 f)), ((nb095_alpha_dummy_387 D R S_cls E),
        (nb095_alpha_dummy_390 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_487 D R S_cls E),
        (nb095_alpha_dummy_490 f)), ((nb095_alpha_dummy_486 D R S_cls E),
        (nb095_alpha_dummy_489 f)), ((nb095_alpha_dummy_485 D R S_cls E),
        (nb095_alpha_dummy_488 f)), ((nb095_alpha_dummy_483 D R S_cls E),
        (nb095_alpha_dummy_484 f)), ((nb095_alpha_dummy_479 D R S_cls E),
        (nb095_alpha_dummy_481 f)), ((nb095_alpha_dummy_480 D R S_cls E),
        (nb095_alpha_dummy_482 f)), ((nb095_alpha_dummy_505 D R S_cls E),
        (nb095_alpha_dummy_506 f)), ((nb095_alpha_dummy_503 D R S_cls E),
        (nb095_alpha_dummy_504 f)), ((nb095_alpha_dummy_472 D R S_cls E),
        (nb095_alpha_dummy_474 f)), ((nb095_alpha_dummy_471 D R S_cls E),
        (nb095_alpha_dummy_473 f)), ((nb095_alpha_dummy_501 D R S_cls E),
        (nb095_alpha_dummy_502 f)), ((nb095_alpha_dummy_475 D R S_cls E),
        (nb095_alpha_dummy_476 f)), ((nb095_alpha_dummy_466 D R S_cls E),
        (nb095_alpha_dummy_468 f)), ((nb095_alpha_dummy_465 D R S_cls E),
        (nb095_alpha_dummy_467 f)), ((nb095_alpha_dummy_469 D R S_cls E),
        (nb095_alpha_dummy_470 f)), ((nb095_alpha_dummy_387 D R S_cls E),
        (nb095_alpha_dummy_390 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_479 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_497 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_479 D R S_cls E) ≠
                                (nb095_alpha_dummy_483 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
                                unfold nb095_alpha_dummy_484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
                            ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
                            ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
                            ((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
                            ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
                            ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
                            ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
                            ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
                            ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
                            ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
                            ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
                            ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
                            ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
                            ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
                            ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
                            ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_479 D R S_cls E) ≠
                              (nb095_alpha_dummy_483 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_483;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0482 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
                              unfold nb095_alpha_dummy_484;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_479 D R S_cls E) ≠
                                (nb095_alpha_dummy_483 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
                                unfold nb095_alpha_dummy_484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
                            ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
                            ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
                            ((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
                            ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
                            ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
                            ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
                            ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
                            ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
                            ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
                            ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
                            ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
                            ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
                            ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
                            ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
                            ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                        (nb095_alpha_dummy_479 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_479;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_481 f) from (by
                        unfold nb095_alpha_dummy_481;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0481 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                          (nb095_alpha_dummy_480 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_480;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E)
                                  1))))
                      (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_482 f) from (by
                          unfold nb095_alpha_dummy_482;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                            (nb095_alpha_dummy_505 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_505;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0510 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_506 f) from (by
                            unfold nb095_alpha_dummy_506;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0511 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_472 D R S_cls E) ≠
                              (nb095_alpha_dummy_503 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_503;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0508 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_474 f) ≠ (nb095_alpha_dummy_504 f) from (by
                              unfold nb095_alpha_dummy_504;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0509 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_472 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_474 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_479 D R S_cls E) ≠
        (nb095_alpha_dummy_486 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_486;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0484 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_481 f) ≠
        (nb095_alpha_dummy_489 f) from (by
                                          unfold nb095_alpha_dummy_489;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0485 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_485 D R S_cls E) from (by
          unfold nb095_alpha_dummy_485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_488 f) from (by
          unfold nb095_alpha_dummy_488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_479 D R S_cls E) ≠ (nb095_alpha_dummy_483 D R S_cls E) from (by
          unfold nb095_alpha_dummy_483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
          unfold nb095_alpha_dummy_484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_487 D R S_cls E),
        (nb095_alpha_dummy_490 f)), ((nb095_alpha_dummy_486 D R S_cls E),
        (nb095_alpha_dummy_489 f)), ((nb095_alpha_dummy_485 D R S_cls E),
        (nb095_alpha_dummy_488 f)), ((nb095_alpha_dummy_483 D R S_cls E),
        (nb095_alpha_dummy_484 f)), ((nb095_alpha_dummy_479 D R S_cls E),
        (nb095_alpha_dummy_481 f)), ((nb095_alpha_dummy_480 D R S_cls E),
        (nb095_alpha_dummy_482 f)), ((nb095_alpha_dummy_505 D R S_cls E),
        (nb095_alpha_dummy_506 f)), ((nb095_alpha_dummy_503 D R S_cls E),
        (nb095_alpha_dummy_504 f)), ((nb095_alpha_dummy_472 D R S_cls E),
        (nb095_alpha_dummy_474 f)), ((nb095_alpha_dummy_471 D R S_cls E),
        (nb095_alpha_dummy_473 f)), ((nb095_alpha_dummy_501 D R S_cls E),
        (nb095_alpha_dummy_502 f)), ((nb095_alpha_dummy_475 D R S_cls E),
        (nb095_alpha_dummy_476 f)), ((nb095_alpha_dummy_466 D R S_cls E),
        (nb095_alpha_dummy_468 f)), ((nb095_alpha_dummy_465 D R S_cls E),
        (nb095_alpha_dummy_467 f)), ((nb095_alpha_dummy_469 D R S_cls E),
        (nb095_alpha_dummy_470 f)), ((nb095_alpha_dummy_387 D R S_cls E),
        (nb095_alpha_dummy_390 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_493 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_494 f) from (by
          unfold
            nb095_alpha_dummy_494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_491 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_492 f) from (by
          unfold
            nb095_alpha_dummy_492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_487 D R S_cls E), (nb095_alpha_dummy_490 f)),
        ((nb095_alpha_dummy_486 D R S_cls E), (nb095_alpha_dummy_489 f)),
        ((nb095_alpha_dummy_485 D R S_cls E), (nb095_alpha_dummy_488 f)),
        ((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
        ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
        ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
        ((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
        ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
        ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
        ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
        ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
        ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_479 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠ (nb095_alpha_dummy_497 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_498 f) from (by
          unfold
            nb095_alpha_dummy_498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_486 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_489 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_479
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_481 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_487 D R S_cls E) ≠ (nb095_alpha_dummy_499 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_500 f) from (by
          unfold
            nb095_alpha_dummy_500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_487 D R S_cls E) ≠
        (nb095_alpha_dummy_495 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_490 f) ≠ (nb095_alpha_dummy_496 f) from (by
          unfold
            nb095_alpha_dummy_496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_479 D R S_cls E) ≠
                                  (nb095_alpha_dummy_483 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_483;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0482 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                (by
                                  unfold nb095_alpha_dummy_484;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
                              ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
                              ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
                              ((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
                              ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
                              ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
                              ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
                              ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
                              ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
                              ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
                              ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
                              ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
                              ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
                              ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
                              ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
                              ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_479 D R S_cls E) ≠
                                (nb095_alpha_dummy_483 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from (by
                                unfold nb095_alpha_dummy_484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_479 D R S_cls E) ≠
                                  (nb095_alpha_dummy_483 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_483;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0482 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_481 f) ≠ (nb095_alpha_dummy_484 f) from
                                (by
                                  unfold nb095_alpha_dummy_484;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_483 D R S_cls E), (nb095_alpha_dummy_484 f)),
                              ((nb095_alpha_dummy_479 D R S_cls E), (nb095_alpha_dummy_481 f)),
                              ((nb095_alpha_dummy_480 D R S_cls E), (nb095_alpha_dummy_482 f)),
                              ((nb095_alpha_dummy_505 D R S_cls E), (nb095_alpha_dummy_506 f)),
                              ((nb095_alpha_dummy_503 D R S_cls E), (nb095_alpha_dummy_504 f)),
                              ((nb095_alpha_dummy_472 D R S_cls E), (nb095_alpha_dummy_474 f)),
                              ((nb095_alpha_dummy_471 D R S_cls E), (nb095_alpha_dummy_473 f)),
                              ((nb095_alpha_dummy_501 D R S_cls E), (nb095_alpha_dummy_502 f)),
                              ((nb095_alpha_dummy_475 D R S_cls E), (nb095_alpha_dummy_476 f)),
                              ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
                              ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
                              ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
                              ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
                              ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
                              ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
                              ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0063 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_513 D R S_cls E), (nb095_alpha_dummy_514 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_513 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_513 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_507 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_508 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_507 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_514 f))
          (Class.cab (nb095_alpha_dummy_509 f)
            (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_514 f))
            (Class.cab (nb095_alpha_dummy_509 f)
              (syn_wrex (nb095_alpha_dummy_510 f) (Class.cv (nb095_alpha_dummy_468 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_509 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_510 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                      (nb095_alpha_dummy_508 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_508;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_510 f) from (by
                      unfold nb095_alpha_dummy_510;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                        (nb095_alpha_dummy_507 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_507;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_509 f) from (by
                        unfold nb095_alpha_dummy_509;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                          (nb095_alpha_dummy_513 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_513;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_514 f) from (by
                          unfold nb095_alpha_dummy_514;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                            (nb095_alpha_dummy_511 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_511;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_512 f) from (by
                            unfold nb095_alpha_dummy_512;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_467 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                              (nb095_alpha_dummy_515 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_515;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_517 f) from (by
                              unfold nb095_alpha_dummy_517;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                                (nb095_alpha_dummy_516 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_516;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_518 f) from (by
                                unfold nb095_alpha_dummy_518;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_510 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_522 D R S_cls E) from (by
          unfold nb095_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_525 f) from (by
          unfold nb095_alpha_dummy_525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_521 D R S_cls E) from (by
          unfold nb095_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_524 f) from (by
          unfold nb095_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_519 D R S_cls E) from (by
          unfold nb095_alpha_dummy_519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
          unfold nb095_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_523 D R S_cls E), (nb095_alpha_dummy_526 f)),
        ((nb095_alpha_dummy_522 D R S_cls E), (nb095_alpha_dummy_525 f)),
        ((nb095_alpha_dummy_521 D R S_cls E), (nb095_alpha_dummy_524 f)),
        ((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
        ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
        ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_513 D R S_cls E), (nb095_alpha_dummy_514 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_522
        D R S_cls E) ≠ (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_523 D R S_cls E), (nb095_alpha_dummy_526 f)),
        ((nb095_alpha_dummy_522 D R S_cls E), (nb095_alpha_dummy_525 f)),
        ((nb095_alpha_dummy_521 D R S_cls E), (nb095_alpha_dummy_524 f)),
        ((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
        ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
        ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_513 D R S_cls E), (nb095_alpha_dummy_514 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_534 f) from (by
          unfold
            nb095_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_534 f) from (by
          unfold
            nb095_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523
        D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_536 f) from (by
          unfold
            nb095_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523
        D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_536 f) from (by
          unfold
            nb095_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_515 D R S_cls E) ≠
                                        (nb095_alpha_dummy_519 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                      (by
                                        unfold nb095_alpha_dummy_520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_519 D R S_cls E),
                                      (nb095_alpha_dummy_520 f)),
                                    ((nb095_alpha_dummy_515 D R S_cls E),
                                      (nb095_alpha_dummy_517 f)),
                                    ((nb095_alpha_dummy_516 D R S_cls E),
                                      (nb095_alpha_dummy_518 f)),
                                    ((nb095_alpha_dummy_508 D R S_cls E),
                                      (nb095_alpha_dummy_510 f)),
                                    ((nb095_alpha_dummy_507 D R S_cls E),
                                      (nb095_alpha_dummy_509 f)),
                                    ((nb095_alpha_dummy_513 D R S_cls E),
                                      (nb095_alpha_dummy_514 f)),
                                    ((nb095_alpha_dummy_511 D R S_cls E),
                                      (nb095_alpha_dummy_512 f)),
                                    ((nb095_alpha_dummy_466 D R S_cls E),
                                      (nb095_alpha_dummy_468 f)),
                                    ((nb095_alpha_dummy_465 D R S_cls E),
                                      (nb095_alpha_dummy_467 f)),
                                    ((nb095_alpha_dummy_469 D R S_cls E),
                                      (nb095_alpha_dummy_470 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_515 D R S_cls E) ≠
                                      (nb095_alpha_dummy_519 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_519;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                    (by
                                      unfold nb095_alpha_dummy_520;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_515 D R S_cls E) ≠
                                        (nb095_alpha_dummy_519 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                      (by
                                        unfold nb095_alpha_dummy_520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_519 D R S_cls E),
                                      (nb095_alpha_dummy_520 f)),
                                    ((nb095_alpha_dummy_515 D R S_cls E),
                                      (nb095_alpha_dummy_517 f)),
                                    ((nb095_alpha_dummy_516 D R S_cls E),
                                      (nb095_alpha_dummy_518 f)),
                                    ((nb095_alpha_dummy_508 D R S_cls E),
                                      (nb095_alpha_dummy_510 f)),
                                    ((nb095_alpha_dummy_507 D R S_cls E),
                                      (nb095_alpha_dummy_509 f)),
                                    ((nb095_alpha_dummy_513 D R S_cls E),
                                      (nb095_alpha_dummy_514 f)),
                                    ((nb095_alpha_dummy_511 D R S_cls E),
                                      (nb095_alpha_dummy_512 f)),
                                    ((nb095_alpha_dummy_466 D R S_cls E),
                                      (nb095_alpha_dummy_468 f)),
                                    ((nb095_alpha_dummy_465 D R S_cls E),
                                      (nb095_alpha_dummy_467 f)),
                                    ((nb095_alpha_dummy_469 D R S_cls E),
                                      (nb095_alpha_dummy_470 f)),
                                    ((nb095_alpha_dummy_387 D R S_cls E),
                                      (nb095_alpha_dummy_390 f)),
                                    ((nb095_alpha_dummy_386 D R S_cls E),
                                      (nb095_alpha_dummy_389 f)),
                                    ((nb095_alpha_dummy_385 D R S_cls E),
                                      (nb095_alpha_dummy_388 f)),
                                    ((nb095_alpha_dummy_391 D R S_cls E),
                                      (nb095_alpha_dummy_392 f)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                        (nb095_alpha_dummy_508 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_508;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_510 f) from (by
                        unfold nb095_alpha_dummy_510;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                          (nb095_alpha_dummy_507 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_507;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_509 f) from (by
                          unfold nb095_alpha_dummy_509;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                            (nb095_alpha_dummy_513 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_513;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_514 f) from (by
                            unfold nb095_alpha_dummy_514;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_466 D R S_cls E) ≠
                              (nb095_alpha_dummy_511 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_511;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_468 f) ≠ (nb095_alpha_dummy_512 f) from (by
                              unfold nb095_alpha_dummy_512;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_466 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_465 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_468 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_467 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_508 D R S_cls E) ≠
                                (nb095_alpha_dummy_515 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_515;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_517 f) from (by
                                unfold nb095_alpha_dummy_517;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                                  (nb095_alpha_dummy_516 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_516;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0518 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_518 f) from
                                (by
                                  unfold nb095_alpha_dummy_518;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_510 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_522 D R S_cls E) from (by
          unfold nb095_alpha_dummy_522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_525 f) from (by
          unfold nb095_alpha_dummy_525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_521 D R S_cls E) from (by
          unfold nb095_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_524 f) from (by
          unfold nb095_alpha_dummy_524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_519 D R S_cls E) from (by
          unfold nb095_alpha_dummy_519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
          unfold nb095_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_523 D R S_cls E), (nb095_alpha_dummy_526 f)),
        ((nb095_alpha_dummy_522 D R S_cls E), (nb095_alpha_dummy_525 f)),
        ((nb095_alpha_dummy_521 D R S_cls E), (nb095_alpha_dummy_524 f)),
        ((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
        ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
        ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_513 D R S_cls E), (nb095_alpha_dummy_514 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_522
        D R S_cls E) ≠ (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_530 f) from (by
          unfold
            nb095_alpha_dummy_530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_527 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_523 D R S_cls E), (nb095_alpha_dummy_526 f)),
        ((nb095_alpha_dummy_522 D R S_cls E), (nb095_alpha_dummy_525 f)),
        ((nb095_alpha_dummy_521 D R S_cls E), (nb095_alpha_dummy_524 f)),
        ((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
        ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
        ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_513 D R S_cls E), (nb095_alpha_dummy_514 f)),
        ((nb095_alpha_dummy_511 D R S_cls E), (nb095_alpha_dummy_512 f)),
        ((nb095_alpha_dummy_466 D R S_cls E), (nb095_alpha_dummy_468 f)),
        ((nb095_alpha_dummy_465 D R S_cls E), (nb095_alpha_dummy_467 f)),
        ((nb095_alpha_dummy_469 D R S_cls E), (nb095_alpha_dummy_470 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_534 f) from (by
          unfold
            nb095_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_534 f) from (by
          unfold
            nb095_alpha_dummy_534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_525 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523
        D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_536 f) from (by
          unfold
            nb095_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523
        D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_536 f) from (by
          unfold
            nb095_alpha_dummy_536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_531 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_532 f) from (by
          unfold
            nb095_alpha_dummy_532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_519 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_517 f) ≠
        (nb095_alpha_dummy_520 f) from (by
                                          unfold nb095_alpha_dummy_520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_519 D R S_cls E),
                                        (nb095_alpha_dummy_520 f)),
                                      ((nb095_alpha_dummy_515 D R S_cls E),
                                        (nb095_alpha_dummy_517 f)),
                                      ((nb095_alpha_dummy_516 D R S_cls E),
                                        (nb095_alpha_dummy_518 f)),
                                      ((nb095_alpha_dummy_508 D R S_cls E),
                                        (nb095_alpha_dummy_510 f)),
                                      ((nb095_alpha_dummy_507 D R S_cls E),
                                        (nb095_alpha_dummy_509 f)),
                                      ((nb095_alpha_dummy_513 D R S_cls E),
                                        (nb095_alpha_dummy_514 f)),
                                      ((nb095_alpha_dummy_511 D R S_cls E),
                                        (nb095_alpha_dummy_512 f)),
                                      ((nb095_alpha_dummy_466 D R S_cls E),
                                        (nb095_alpha_dummy_468 f)),
                                      ((nb095_alpha_dummy_465 D R S_cls E),
                                        (nb095_alpha_dummy_467 f)),
                                      ((nb095_alpha_dummy_469 D R S_cls E),
                                        (nb095_alpha_dummy_470 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_515 D R S_cls E) ≠
                                        (nb095_alpha_dummy_519 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                      (by
                                        unfold nb095_alpha_dummy_520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_519 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_517 f) ≠
        (nb095_alpha_dummy_520 f) from (by
                                          unfold nb095_alpha_dummy_520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_519 D R S_cls E),
                                        (nb095_alpha_dummy_520 f)),
                                      ((nb095_alpha_dummy_515 D R S_cls E),
                                        (nb095_alpha_dummy_517 f)),
                                      ((nb095_alpha_dummy_516 D R S_cls E),
                                        (nb095_alpha_dummy_518 f)),
                                      ((nb095_alpha_dummy_508 D R S_cls E),
                                        (nb095_alpha_dummy_510 f)),
                                      ((nb095_alpha_dummy_507 D R S_cls E),
                                        (nb095_alpha_dummy_509 f)),
                                      ((nb095_alpha_dummy_513 D R S_cls E),
                                        (nb095_alpha_dummy_514 f)),
                                      ((nb095_alpha_dummy_511 D R S_cls E),
                                        (nb095_alpha_dummy_512 f)),
                                      ((nb095_alpha_dummy_466 D R S_cls E),
                                        (nb095_alpha_dummy_468 f)),
                                      ((nb095_alpha_dummy_465 D R S_cls E),
                                        (nb095_alpha_dummy_467 f)),
                                      ((nb095_alpha_dummy_469 D R S_cls E),
                                        (nb095_alpha_dummy_470 f)),
                                      ((nb095_alpha_dummy_387 D R S_cls E),
                                        (nb095_alpha_dummy_390 f)),
                                      ((nb095_alpha_dummy_386 D R S_cls E),
                                        (nb095_alpha_dummy_389 f)),
                                      ((nb095_alpha_dummy_385 D R S_cls E),
                                        (nb095_alpha_dummy_388 f)),
                                      ((nb095_alpha_dummy_391 D R S_cls E),
                                        (nb095_alpha_dummy_392 f)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
