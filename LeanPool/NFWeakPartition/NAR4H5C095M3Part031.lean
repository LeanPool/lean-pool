/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part030

/-! NF weak partition development: NAR4H5C095M3Part031. -/


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
noncomputable def nb095_split_alpha_0064 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
        ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_541 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_541 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_508 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_542 f))
          (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_542 f))
            (syn_cphi (Class.cv (nb095_alpha_dummy_510 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                      (nb095_alpha_dummy_515 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_515;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_517 f) from (by
                      unfold nb095_alpha_dummy_517;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                        (nb095_alpha_dummy_516 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_516;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_518 f) from (by
                        unfold nb095_alpha_dummy_518;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0519 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                          (nb095_alpha_dummy_541 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_541;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0548 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_542 f) from (by
                          unfold nb095_alpha_dummy_542;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0549 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                            (nb095_alpha_dummy_539 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_539;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0546 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_540 f) from (by
                            unfold nb095_alpha_dummy_540;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0547 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_510 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_515 D R S_cls E) ≠
                                        (nb095_alpha_dummy_522 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0522 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_525 f) from
                                      (by
                                        unfold nb095_alpha_dummy_525;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0523 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_521 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0522 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_517 f) ≠
        (nb095_alpha_dummy_524 f) from (by
                                          unfold nb095_alpha_dummy_524;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0523 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_519 D R S_cls E) from (by
          unfold nb095_alpha_dummy_519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
          unfold nb095_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_523 D R S_cls E),
        (nb095_alpha_dummy_526 f)), ((nb095_alpha_dummy_522 D R S_cls E),
        (nb095_alpha_dummy_525 f)), ((nb095_alpha_dummy_521 D R S_cls E),
        (nb095_alpha_dummy_524 f)), ((nb095_alpha_dummy_519 D R S_cls E),
        (nb095_alpha_dummy_520 f)), ((nb095_alpha_dummy_515 D R S_cls E),
        (nb095_alpha_dummy_517 f)), ((nb095_alpha_dummy_516 D R S_cls E),
        (nb095_alpha_dummy_518 f)), ((nb095_alpha_dummy_541 D R S_cls E),
        (nb095_alpha_dummy_542 f)), ((nb095_alpha_dummy_539 D R S_cls E),
        (nb095_alpha_dummy_540 f)), ((nb095_alpha_dummy_508 D R S_cls E),
        (nb095_alpha_dummy_510 f)), ((nb095_alpha_dummy_507 D R S_cls E),
        (nb095_alpha_dummy_509 f)), ((nb095_alpha_dummy_537 D R S_cls E),
        (nb095_alpha_dummy_538 f)), ((nb095_alpha_dummy_511 D R S_cls E),
        (nb095_alpha_dummy_512 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠
        (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        [((nb095_alpha_dummy_523 D R S_cls E),
        (nb095_alpha_dummy_526 f)), ((nb095_alpha_dummy_522 D R S_cls E),
        (nb095_alpha_dummy_525 f)), ((nb095_alpha_dummy_521 D R S_cls E),
        (nb095_alpha_dummy_524 f)), ((nb095_alpha_dummy_519 D R S_cls E),
        (nb095_alpha_dummy_520 f)), ((nb095_alpha_dummy_515 D R S_cls E),
        (nb095_alpha_dummy_517 f)), ((nb095_alpha_dummy_516 D R S_cls E),
        (nb095_alpha_dummy_518 f)), ((nb095_alpha_dummy_541 D R S_cls E),
        (nb095_alpha_dummy_542 f)), ((nb095_alpha_dummy_539 D R S_cls E),
        (nb095_alpha_dummy_540 f)), ((nb095_alpha_dummy_508 D R S_cls E),
        (nb095_alpha_dummy_510 f)), ((nb095_alpha_dummy_507 D R S_cls E),
        (nb095_alpha_dummy_509 f)), ((nb095_alpha_dummy_537 D R S_cls E),
        (nb095_alpha_dummy_538 f)), ((nb095_alpha_dummy_511 D R S_cls E),
        (nb095_alpha_dummy_512 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_515 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠
        (nb095_alpha_dummy_533 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
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
                    D R S_cls E)
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
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
                                unfold nb095_alpha_dummy_520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
                            ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
                            ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
                            ((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
                            ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
                            ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
                            ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
                            ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_515 D R S_cls E) ≠
                              (nb095_alpha_dummy_519 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_519;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0520 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
                              unfold nb095_alpha_dummy_520;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_515 D R S_cls E) ≠
                                (nb095_alpha_dummy_519 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
                                unfold nb095_alpha_dummy_520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
                            ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
                            ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
                            ((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
                            ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
                            ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
                            ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
                            ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                        (nb095_alpha_dummy_515 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_515;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_517 f) from (by
                        unfold nb095_alpha_dummy_517;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0519 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                          (nb095_alpha_dummy_516 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E)
                                  1))))
                      (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_518 f) from (by
                          unfold nb095_alpha_dummy_518;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                            (nb095_alpha_dummy_541 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_541;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0548 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_542 f) from (by
                            unfold nb095_alpha_dummy_542;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0549 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_508 D R S_cls E) ≠
                              (nb095_alpha_dummy_539 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_539;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0546 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_510 f) ≠ (nb095_alpha_dummy_540 f) from (by
                              unfold nb095_alpha_dummy_540;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0547 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_508 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_510 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_515 D R S_cls E) ≠
        (nb095_alpha_dummy_522 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0522 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_517 f) ≠
        (nb095_alpha_dummy_525 f) from (by
                                          unfold nb095_alpha_dummy_525;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0523 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_515 D R S_cls E) ≠ (nb095_alpha_dummy_521 D R S_cls E) from (by
          unfold nb095_alpha_dummy_521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R S_cls E)
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
                  (nb095_support_mem_0520 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
          unfold nb095_alpha_dummy_520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_523 D R S_cls E),
        (nb095_alpha_dummy_526 f)), ((nb095_alpha_dummy_522 D R S_cls E),
        (nb095_alpha_dummy_525 f)), ((nb095_alpha_dummy_521 D R S_cls E),
        (nb095_alpha_dummy_524 f)), ((nb095_alpha_dummy_519 D R S_cls E),
        (nb095_alpha_dummy_520 f)), ((nb095_alpha_dummy_515 D R S_cls E),
        (nb095_alpha_dummy_517 f)), ((nb095_alpha_dummy_516 D R S_cls E),
        (nb095_alpha_dummy_518 f)), ((nb095_alpha_dummy_541 D R S_cls E),
        (nb095_alpha_dummy_542 f)), ((nb095_alpha_dummy_539 D R S_cls E),
        (nb095_alpha_dummy_540 f)), ((nb095_alpha_dummy_508 D R S_cls E),
        (nb095_alpha_dummy_510 f)), ((nb095_alpha_dummy_507 D R S_cls E),
        (nb095_alpha_dummy_509 f)), ((nb095_alpha_dummy_537 D R S_cls E),
        (nb095_alpha_dummy_538 f)), ((nb095_alpha_dummy_511 D R S_cls E),
        (nb095_alpha_dummy_512 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
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
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_526 f) ≠ (nb095_alpha_dummy_528 f) from (by
          unfold
            nb095_alpha_dummy_528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_529 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls E)
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
                    D R S_cls E)
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
        ((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
        ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
        ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
        ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
        ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_515 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_515 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_517 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_522 D R S_cls E) ≠ (nb095_alpha_dummy_533 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_523 D R S_cls E) ≠ (nb095_alpha_dummy_535 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls E)
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
                    D R S_cls E)
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
                                          (nb095_support_mem_0520 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                (by
                                  unfold nb095_alpha_dummy_520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
                              ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
                              ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
                              ((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
                              ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
                              ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
                              ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
                              ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
                                        (nb095_support_mem_0520 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from (by
                                unfold nb095_alpha_dummy_520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_515 D R S_cls E) ≠
                                  (nb095_alpha_dummy_519 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_519;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0520 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_517 f) ≠ (nb095_alpha_dummy_520 f) from
                                (by
                                  unfold nb095_alpha_dummy_520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0521 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_519 D R S_cls E), (nb095_alpha_dummy_520 f)),
                              ((nb095_alpha_dummy_515 D R S_cls E), (nb095_alpha_dummy_517 f)),
                              ((nb095_alpha_dummy_516 D R S_cls E), (nb095_alpha_dummy_518 f)),
                              ((nb095_alpha_dummy_541 D R S_cls E), (nb095_alpha_dummy_542 f)),
                              ((nb095_alpha_dummy_539 D R S_cls E), (nb095_alpha_dummy_540 f)),
                              ((nb095_alpha_dummy_508 D R S_cls E), (nb095_alpha_dummy_510 f)),
                              ((nb095_alpha_dummy_507 D R S_cls E), (nb095_alpha_dummy_509 f)),
                              ((nb095_alpha_dummy_537 D R S_cls E), (nb095_alpha_dummy_538 f)),
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
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0065 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_103 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_103 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_097 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_098 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_097 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_104 f))
          (Class.cab (nb095_alpha_dummy_099 f)
            (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_104 f))
            (Class.cab (nb095_alpha_dummy_099 f)
              (syn_wrex (nb095_alpha_dummy_100 f) (Class.cv (nb095_alpha_dummy_093 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_099 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                      (nb095_alpha_dummy_098 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
                      unfold nb095_alpha_dummy_100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                        (nb095_alpha_dummy_097 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
                        unfold nb095_alpha_dummy_099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                          (nb095_alpha_dummy_103 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_104 f) from (by
                          unfold nb095_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                            (nb095_alpha_dummy_101 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_102 f) from (by
                            unfold nb095_alpha_dummy_102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                              (nb095_alpha_dummy_105 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                              unfold nb095_alpha_dummy_107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                                (nb095_alpha_dummy_106 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                                unfold nb095_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_112 D R S_cls E) from (by
          unfold nb095_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from (by
          unfold nb095_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112
        D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_109 D R S_cls E),
                                      (nb095_alpha_dummy_110 f)),
                                    ((nb095_alpha_dummy_105 D R S_cls E),
                                      (nb095_alpha_dummy_107 f)),
                                    ((nb095_alpha_dummy_106 D R S_cls E),
                                      (nb095_alpha_dummy_108 f)),
                                    ((nb095_alpha_dummy_098 D R S_cls E),
                                      (nb095_alpha_dummy_100 f)),
                                    ((nb095_alpha_dummy_097 D R S_cls E),
                                      (nb095_alpha_dummy_099 f)),
                                    ((nb095_alpha_dummy_103 D R S_cls E),
                                      (nb095_alpha_dummy_104 f)),
                                    ((nb095_alpha_dummy_101 D R S_cls E),
                                      (nb095_alpha_dummy_102 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
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
                                    (nb095_alpha_dummy_105 D R S_cls E) ≠
                                      (nb095_alpha_dummy_109 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                    (by
                                      unfold nb095_alpha_dummy_110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_109 D R S_cls E),
                                      (nb095_alpha_dummy_110 f)),
                                    ((nb095_alpha_dummy_105 D R S_cls E),
                                      (nb095_alpha_dummy_107 f)),
                                    ((nb095_alpha_dummy_106 D R S_cls E),
                                      (nb095_alpha_dummy_108 f)),
                                    ((nb095_alpha_dummy_098 D R S_cls E),
                                      (nb095_alpha_dummy_100 f)),
                                    ((nb095_alpha_dummy_097 D R S_cls E),
                                      (nb095_alpha_dummy_099 f)),
                                    ((nb095_alpha_dummy_103 D R S_cls E),
                                      (nb095_alpha_dummy_104 f)),
                                    ((nb095_alpha_dummy_101 D R S_cls E),
                                      (nb095_alpha_dummy_102 f)),
                                    ((nb095_alpha_dummy_092 D R S_cls E),
                                      (nb095_alpha_dummy_094 f)),
                                    ((nb095_alpha_dummy_091 D R S_cls E),
                                      (nb095_alpha_dummy_093 f)),
                                    ((nb095_alpha_dummy_095 D R S_cls E),
                                      (nb095_alpha_dummy_096 f)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                        (nb095_alpha_dummy_098 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_100 f) from (by
                        unfold nb095_alpha_dummy_100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                          (nb095_alpha_dummy_097 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_099 f) from (by
                          unfold nb095_alpha_dummy_099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                            (nb095_alpha_dummy_103 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_104 f) from (by
                            unfold nb095_alpha_dummy_104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_091 D R S_cls E) ≠
                              (nb095_alpha_dummy_101 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_093 f) ≠ (nb095_alpha_dummy_102 f) from (by
                              unfold nb095_alpha_dummy_102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_093 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_098 D R S_cls E) ≠
                                (nb095_alpha_dummy_105 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                                unfold nb095_alpha_dummy_107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                                  (nb095_alpha_dummy_106 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from
                                (by
                                  unfold nb095_alpha_dummy_108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_112 D R S_cls E) from (by
          unfold nb095_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from (by
          unfold nb095_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112
        D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113
        D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_110 f) from (by
                                          unfold nb095_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_109 D R S_cls E),
                                        (nb095_alpha_dummy_110 f)),
                                      ((nb095_alpha_dummy_105 D R S_cls E),
                                        (nb095_alpha_dummy_107 f)),
                                      ((nb095_alpha_dummy_106 D R S_cls E),
                                        (nb095_alpha_dummy_108 f)),
                                      ((nb095_alpha_dummy_098 D R S_cls E),
                                        (nb095_alpha_dummy_100 f)),
                                      ((nb095_alpha_dummy_097 D R S_cls E),
                                        (nb095_alpha_dummy_099 f)),
                                      ((nb095_alpha_dummy_103 D R S_cls E),
                                        (nb095_alpha_dummy_104 f)),
                                      ((nb095_alpha_dummy_101 D R S_cls E),
                                        (nb095_alpha_dummy_102 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
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
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                      (by
                                        unfold nb095_alpha_dummy_110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_109 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_110 f) from (by
                                          unfold nb095_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_109 D R S_cls E),
                                        (nb095_alpha_dummy_110 f)),
                                      ((nb095_alpha_dummy_105 D R S_cls E),
                                        (nb095_alpha_dummy_107 f)),
                                      ((nb095_alpha_dummy_106 D R S_cls E),
                                        (nb095_alpha_dummy_108 f)),
                                      ((nb095_alpha_dummy_098 D R S_cls E),
                                        (nb095_alpha_dummy_100 f)),
                                      ((nb095_alpha_dummy_097 D R S_cls E),
                                        (nb095_alpha_dummy_099 f)),
                                      ((nb095_alpha_dummy_103 D R S_cls E),
                                        (nb095_alpha_dummy_104 f)),
                                      ((nb095_alpha_dummy_101 D R S_cls E),
                                        (nb095_alpha_dummy_102 f)),
                                      ((nb095_alpha_dummy_092 D R S_cls E),
                                        (nb095_alpha_dummy_094 f)),
                                      ((nb095_alpha_dummy_091 D R S_cls E),
                                        (nb095_alpha_dummy_093 f)),
                                      ((nb095_alpha_dummy_095 D R S_cls E),
                                        (nb095_alpha_dummy_096 f)),
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
noncomputable def nb095_split_alpha_0066 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
        ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_131 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_131 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_098 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_132 f))
          (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_132 f))
            (syn_cphi (Class.cv (nb095_alpha_dummy_100 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                      (nb095_alpha_dummy_105 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_105;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                      unfold nb095_alpha_dummy_107;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                        (nb095_alpha_dummy_106 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_106;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                        unfold nb095_alpha_dummy_108;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                          (nb095_alpha_dummy_131 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_132 f) from (by
                          unfold nb095_alpha_dummy_132;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                            (nb095_alpha_dummy_129 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_130 f) from (by
                            unfold nb095_alpha_dummy_130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_105 D R S_cls E) ≠
                                        (nb095_alpha_dummy_112 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0094 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_115 f) from
                                      (by
                                        unfold nb095_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0095 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_111 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_114 f) from (by
                                          unfold nb095_alpha_dummy_114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_105 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                            ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                            ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                            ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                            ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                            ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                            ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                            ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                            ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                            ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                            ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                            ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
                        (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
                              (nb095_alpha_dummy_109 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_109;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0092 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                              unfold nb095_alpha_dummy_110;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                            ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                            ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                            ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                            ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                            ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                            ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                            ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                            ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                            ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                            ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                            ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                        (nb095_alpha_dummy_105 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_105;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_107 f) from (by
                        unfold nb095_alpha_dummy_107;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0091 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                          (nb095_alpha_dummy_106 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                  1))))
                      (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_108 f) from (by
                          unfold nb095_alpha_dummy_108;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                            (nb095_alpha_dummy_131 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_131;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0120 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_132 f) from (by
                            unfold nb095_alpha_dummy_132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0121 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_098 D R S_cls E) ≠
                              (nb095_alpha_dummy_129 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0118 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_100 f) ≠ (nb095_alpha_dummy_130 f) from (by
                              unfold nb095_alpha_dummy_130;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0119 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_098 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_100 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_105 D R S_cls E) ≠
        (nb095_alpha_dummy_112 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0094 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_107 f) ≠
        (nb095_alpha_dummy_115 f) from (by
                                          unfold nb095_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0095 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_111 D R S_cls E) from (by
          unfold nb095_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_114 f) from (by
          unfold nb095_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_105 D R S_cls E) ≠ (nb095_alpha_dummy_109 D R S_cls E) from (by
          unfold nb095_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
          unfold nb095_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_113 D R S_cls E),
        (nb095_alpha_dummy_116 f)), ((nb095_alpha_dummy_112 D R S_cls E),
        (nb095_alpha_dummy_115 f)), ((nb095_alpha_dummy_111 D R S_cls E),
        (nb095_alpha_dummy_114 f)), ((nb095_alpha_dummy_109 D R S_cls E),
        (nb095_alpha_dummy_110 f)), ((nb095_alpha_dummy_105 D R S_cls E),
        (nb095_alpha_dummy_107 f)), ((nb095_alpha_dummy_106 D R S_cls E),
        (nb095_alpha_dummy_108 f)), ((nb095_alpha_dummy_131 D R S_cls E),
        (nb095_alpha_dummy_132 f)), ((nb095_alpha_dummy_129 D R S_cls E),
        (nb095_alpha_dummy_130 f)), ((nb095_alpha_dummy_098 D R S_cls E),
        (nb095_alpha_dummy_100 f)), ((nb095_alpha_dummy_097 D R S_cls E),
        (nb095_alpha_dummy_099 f)), ((nb095_alpha_dummy_127 D R S_cls E),
        (nb095_alpha_dummy_128 f)), ((nb095_alpha_dummy_101 D R S_cls E),
        (nb095_alpha_dummy_102 f)), ((nb095_alpha_dummy_092 D R S_cls E),
        (nb095_alpha_dummy_094 f)), ((nb095_alpha_dummy_091 D R S_cls E),
        (nb095_alpha_dummy_093 f)), ((nb095_alpha_dummy_095 D R S_cls E),
        (nb095_alpha_dummy_096 f)), ((nb095_alpha_dummy_466 D R S_cls E),
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
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_119 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_120 f) from (by
          unfold
            nb095_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_117 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_118 f) from (by
          unfold
            nb095_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_113 D R S_cls E), (nb095_alpha_dummy_116 f)),
        ((nb095_alpha_dummy_112 D R S_cls E), (nb095_alpha_dummy_115 f)),
        ((nb095_alpha_dummy_111 D R S_cls E), (nb095_alpha_dummy_114 f)),
        ((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
        ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
        ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
        ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
        ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
        ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
        ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
        ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105 D R S_cls
        E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠ (nb095_alpha_dummy_123 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_124 f) from (by
          unfold
            nb095_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_112 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_115 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_105
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_107 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_113 D R S_cls E) ≠ (nb095_alpha_dummy_125 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_126 f) from (by
          unfold
            nb095_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_113 D R S_cls E) ≠
        (nb095_alpha_dummy_121 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_116 f) ≠ (nb095_alpha_dummy_122 f) from (by
          unfold
            nb095_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_105 D R S_cls E) ≠
                                  (nb095_alpha_dummy_109 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                (by
                                  unfold nb095_alpha_dummy_110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                              ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                              ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                              ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                              ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                              ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                              ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                              ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                              ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                              ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                              ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                              ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
                              (nb095_alpha_dummy_105 D R S_cls E) ≠
                                (nb095_alpha_dummy_109 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0092 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from (by
                                unfold nb095_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095_alpha_dummy_105 D R S_cls E) ≠
                                  (nb095_alpha_dummy_109 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0092 D R S_cls E) 0))))
                              (show (nb095_alpha_dummy_107 f) ≠ (nb095_alpha_dummy_110 f) from
                                (by
                                  unfold nb095_alpha_dummy_110;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0093 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb095_alpha_dummy_109 D R S_cls E), (nb095_alpha_dummy_110 f)),
                              ((nb095_alpha_dummy_105 D R S_cls E), (nb095_alpha_dummy_107 f)),
                              ((nb095_alpha_dummy_106 D R S_cls E), (nb095_alpha_dummy_108 f)),
                              ((nb095_alpha_dummy_131 D R S_cls E), (nb095_alpha_dummy_132 f)),
                              ((nb095_alpha_dummy_129 D R S_cls E), (nb095_alpha_dummy_130 f)),
                              ((nb095_alpha_dummy_098 D R S_cls E), (nb095_alpha_dummy_100 f)),
                              ((nb095_alpha_dummy_097 D R S_cls E), (nb095_alpha_dummy_099 f)),
                              ((nb095_alpha_dummy_127 D R S_cls E), (nb095_alpha_dummy_128 f)),
                              ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
                              ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
                              ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
                              ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
