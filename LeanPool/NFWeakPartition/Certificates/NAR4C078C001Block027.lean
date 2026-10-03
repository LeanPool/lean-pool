/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block026

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part087`. -/


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
noncomputable def nb078_split_alpha_0059 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
        ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_561))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_561)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb078_alpha_dummy_562 g))
            (syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))
          (Wff.classMem (Class.cv (nb078_alpha_dummy_562 g))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_563) from (by
                                    unfold nb078_alpha_dummy_563;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0576) 0)))) (show
                                  (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_564 g) from (by
                                    unfold nb078_alpha_dummy_564;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0577 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_561) from
                                    (by
                                      unfold nb078_alpha_dummy_561;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0574)
                                              0)))) (show
                                    (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_562 g) from
                                    (by
                                      unfold nb078_alpha_dummy_562;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0575 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
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
                                      ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
                                      ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
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
                                      ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
                                      ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
                                      ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                      ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                      ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                      ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                      ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
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
                              (TAlphaVar.there
                                (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_563) from (by
                                    unfold nb078_alpha_dummy_563;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0576) 0)))) (show
                                  (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_564 g) from (by
                                    unfold nb078_alpha_dummy_564;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0577 g)
                                            0)))) (TAlphaVar.there
                                  (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_561) from
                                    (by
                                      unfold nb078_alpha_dummy_561;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0574)
                                              0)))) (show
                                    (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_562 g) from
                                    (by
                                      unfold nb078_alpha_dummy_562;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0575 g)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
        ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)), ((nb078_alpha_dummy_001), g),
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
                                      ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
                                      ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
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
                                      ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
                                      ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
                                      ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                                      ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                                      ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
                                      ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                                      ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                                      ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                                      ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
                                      ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
                                      ((nb078_alpha_dummy_001), g),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
            ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
            ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
            ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
            ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
            ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
            ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
            ((nb078_alpha_dummy_523), (nb078_alpha_dummy_524 x g)),
            ((nb078_alpha_dummy_521), (nb078_alpha_dummy_522 x g)),
            ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
            ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part088`. -/


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
noncomputable def nb078_split_alpha_0060 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
        ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_530))
          (Class.cv (nb078_alpha_dummy_525))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530))) (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_532 g))
          (Class.cv (nb078_alpha_dummy_527 g))) (Wff.neg
          (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
            (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_530) from (by
              unfold nb078_alpha_dummy_530;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 1))))
          (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_532 g) from (by
              unfold nb078_alpha_dummy_532;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 1))))
          (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_529) from (by
                unfold nb078_alpha_dummy_529;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0568) 0))))
            (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_531 g) from (by
                unfold nb078_alpha_dummy_531;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0570 g) 0))))
            (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_559) from (by
                  unfold nb078_alpha_dummy_559;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0572) 0))))
              (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_560 g) from (by
                  unfold nb078_alpha_dummy_560;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0573 g) 0))))
              (TAlphaVar.there (show (nb078_alpha_dummy_525) ≠ (nb078_alpha_dummy_533) from (by
                    unfold nb078_alpha_dummy_533;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0569) 0))))
                (show (nb078_alpha_dummy_527 g) ≠ (nb078_alpha_dummy_534 g) from (by
                    unfold nb078_alpha_dummy_534;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0571 g) 0))))
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_001))).fv ∪ ((syn_cvv)).fv) (by decide))
                  (freshVar_injective (((Class.cv g)).fv ∪ ((syn_cvv)).fv) (by decide))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_526))).fv ∪
                ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
                ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from (by
                                        unfold nb078_alpha_dummy_537;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                0)))) (show (nb078_alpha_dummy_532 g) ≠
                                        (nb078_alpha_dummy_539 g) from (by
                                        unfold nb078_alpha_dummy_539;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from
                                        (by
                                          unfold nb078_alpha_dummy_538;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0546)
                                                  1)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_540 g) from (by
                                          unfold nb078_alpha_dummy_540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0547 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_530) ≠
        (nb078_alpha_dummy_563) from (by
          unfold nb078_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0576) 0)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_564 g) from (by
          unfold nb078_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0577 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_561) from (by
          unfold nb078_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0574) 0)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_562 g) from (by
          unfold nb078_alpha_dummy_562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0575 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_532 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_544) from (by
          unfold nb078_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543)
        from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541)
        from (by
          unfold
            nb078_alpha_dummy_541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_542 g) from (by
          unfold
            nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541)
        from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
        ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538),
        (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
        ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
        ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538),
        (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
        ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from (by
                                        unfold nb078_alpha_dummy_537;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                0)))) (show (nb078_alpha_dummy_532 g) ≠
                                        (nb078_alpha_dummy_539 g) from (by
                                        unfold nb078_alpha_dummy_539;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                0)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from
                                        (by
                                          unfold nb078_alpha_dummy_538;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0546)
                                                  1)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_540 g) from (by
                                          unfold nb078_alpha_dummy_540;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0547 g) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_530) ≠
        (nb078_alpha_dummy_563) from (by
          unfold nb078_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0576) 0)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_564 g) from (by
          unfold nb078_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0577 g) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_561) from (by
          unfold nb078_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0574) 0)))) (show (nb078_alpha_dummy_532 g) ≠
        (nb078_alpha_dummy_562 g) from (by
          unfold nb078_alpha_dummy_562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0575 g) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb078_alpha_dummy_532 g))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_544) from (by
          unfold nb078_alpha_dummy_544;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  1)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543)
        from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541)
        from (by
          unfold
            nb078_alpha_dummy_541;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0548)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_542 g) from (by
          unfold
            nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549
                    g)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_545), (nb078_alpha_dummy_548 g)), ((nb078_alpha_dummy_544),
        (nb078_alpha_dummy_547 g)), ((nb078_alpha_dummy_543), (nb078_alpha_dummy_546 g)),
        ((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537),
        (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)),
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)), ((nb078_alpha_dummy_561),
        (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
        ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)), ((nb078_alpha_dummy_559),
        (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)), ((nb078_alpha_dummy_525),
        (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541)
        from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
        ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538),
        (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
        ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541), (nb078_alpha_dummy_542 g)),
        ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)), ((nb078_alpha_dummy_538),
        (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_563), (nb078_alpha_dummy_564 g)),
        ((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb078_alpha_dummy_561), (nb078_alpha_dummy_562 g)),
                    ((nb078_alpha_dummy_530), (nb078_alpha_dummy_532 g)),
                    ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
                    ((nb078_alpha_dummy_559), (nb078_alpha_dummy_560 g)),
                    ((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
                    ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
                    ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
                    ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
                    ((nb078_alpha_dummy_003), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb078_split_alpha_0061 (x : Var) (y : Var) (g : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_533), (nb078_alpha_dummy_534 g)),
        ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)),
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_533)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_529)
              (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_526))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_530)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_533)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_529)
                (syn_wrex (nb078_alpha_dummy_530) (Class.cv (nb078_alpha_dummy_525))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_529))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_530)))
                      (syn_csn (syn_c0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_534 g)) (syn_ccompl
            (Class.cab (nb078_alpha_dummy_531 g)
              (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_528 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_534 g)) (syn_ccompl
              (Class.cab (nb078_alpha_dummy_531 g)
                (syn_wrex (nb078_alpha_dummy_532 g) (Class.cv (nb078_alpha_dummy_527 g))
                  (Wff.classEq (Class.cv (nb078_alpha_dummy_531 g))
                    (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_532 g)))
                      (syn_csn (syn_c0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from (by
                              unfold nb078_alpha_dummy_530;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                          (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
                              unfold nb078_alpha_dummy_532;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                          (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_536 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0541) 0)))) (show
                                  (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_534 g) from (by
                                    unfold nb078_alpha_dummy_534;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0543 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_526))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from
                                    (by
                                      unfold nb078_alpha_dummy_537;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0546)
                                              0)))) (show
                                    (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_539 g) from
                                    (by
                                      unfold nb078_alpha_dummy_539;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0547 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from (by
                                        unfold nb078_alpha_dummy_538;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                1)))) (show (nb078_alpha_dummy_532 g) ≠
                                        (nb078_alpha_dummy_540 g) from (by
                                        unfold nb078_alpha_dummy_540;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide))
                                  (freshVar_injective
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
                  (nb078_support_mem_0550)
                  1)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543)
        from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
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
                  (nb078_support_mem_0549
                    g)
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
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
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
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_542 g) from (by
          unfold nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541),
        (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
        ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠
        (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541),
        (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
        ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc]))))))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_526) ≠ (nb078_alpha_dummy_530) from (by
                              unfold nb078_alpha_dummy_530;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0540) 1))))
                          (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_532 g) from (by
                              unfold nb078_alpha_dummy_532;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0542 g) 1))))
                          (TAlphaVar.there
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
                              (show (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_536 g) from
                                (by
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
                                          (mem_lt_freshVar (nb078_support_mem_0541) 0)))) (show
                                  (nb078_alpha_dummy_528 g) ≠ (nb078_alpha_dummy_534 g) from (by
                                    unfold nb078_alpha_dummy_534;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb078_support_mem_0543 g)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb078_alpha_dummy_526))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_525))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_528 g))).fv ∪
                              ((Class.cv (nb078_alpha_dummy_527 g))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_537) from
                                    (by
                                      unfold nb078_alpha_dummy_537;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0546)
                                              0)))) (show
                                    (nb078_alpha_dummy_532 g) ≠ (nb078_alpha_dummy_539 g) from
                                    (by
                                      unfold nb078_alpha_dummy_539;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0547 g)
                                              0)))) (TAlphaVar.there (show
                                      (nb078_alpha_dummy_530) ≠ (nb078_alpha_dummy_538) from (by
                                        unfold nb078_alpha_dummy_538;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0546)
                                                1)))) (show (nb078_alpha_dummy_532 g) ≠
                                        (nb078_alpha_dummy_540 g) from (by
                                        unfold nb078_alpha_dummy_540;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0547 g)
                                                1)))) (TAlphaVar.here _ _ _)))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective
                                    (((Class.cv (nb078_alpha_dummy_530))).fv) (by decide))
                                  (freshVar_injective
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
                  (nb078_support_mem_0550)
                  1)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_547 g) from (by
          unfold nb078_alpha_dummy_547;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551 g)
                  1)))) (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠ (nb078_alpha_dummy_543)
        from (by
          unfold nb078_alpha_dummy_543;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0550)
                  0)))) (show (nb078_alpha_dummy_539 g) ≠ (nb078_alpha_dummy_546 g) from (by
          unfold nb078_alpha_dummy_546;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0551
                    g)
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
                  (nb078_support_mem_0549
                    g)
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
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_545) ≠
        (nb078_alpha_dummy_551) from (by
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
        ((nb078_alpha_dummy_001), g), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_537))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539
        g))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_544) ≠ (nb078_alpha_dummy_555) from (by
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
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
        (nb078_alpha_dummy_537))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_539 g))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
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
                (mem_lt_freshVar
                  (nb078_support_mem_0548) 0)))) (show (nb078_alpha_dummy_539 g) ≠
        (nb078_alpha_dummy_542 g) from (by
          unfold nb078_alpha_dummy_542;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541),
        (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
        ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb078_alpha_dummy_537) ≠
        (nb078_alpha_dummy_541) from (by
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
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
                  (nb078_support_mem_0549 g) 0)))) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_541),
        (nb078_alpha_dummy_542 g)), ((nb078_alpha_dummy_537), (nb078_alpha_dummy_539 g)),
        ((nb078_alpha_dummy_538), (nb078_alpha_dummy_540 g)), ((nb078_alpha_dummy_530),
        (nb078_alpha_dummy_532 g)), ((nb078_alpha_dummy_529), (nb078_alpha_dummy_531 g)),
        ((nb078_alpha_dummy_535), (nb078_alpha_dummy_536 g)), ((nb078_alpha_dummy_533),
        (nb078_alpha_dummy_534 g)), ((nb078_alpha_dummy_526), (nb078_alpha_dummy_528 g)),
        ((nb078_alpha_dummy_525), (nb078_alpha_dummy_527 g)), ((nb078_alpha_dummy_001), g),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)] (syn_cnnc)
        (by simp only [fv_syn_cnnc])))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0060 x y g)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.neg (nb078_split_alpha_0060 x y g)))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
