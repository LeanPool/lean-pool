/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part032

/-! NF weak partition development: NAR4H5C095M3Part033. -/


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
noncomputable def nb095_split_alpha_0070 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_549 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_549 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_543 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_544 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_543 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_550 f))
          (Class.cab (nb095_alpha_dummy_545 f)
            (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_550 f))
            (Class.cab (nb095_alpha_dummy_545 f)
              (syn_wrex (nb095_alpha_dummy_546 f) (Class.cv (nb095_alpha_dummy_390 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_545 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_546 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                      (nb095_alpha_dummy_544 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_544;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
                      unfold nb095_alpha_dummy_546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                        (nb095_alpha_dummy_543 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_543;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
                        unfold nb095_alpha_dummy_545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                          (nb095_alpha_dummy_549 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_549;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_550 f) from (by
                          unfold nb095_alpha_dummy_550;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                            (nb095_alpha_dummy_547 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_547;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_548 f) from (by
                            unfold nb095_alpha_dummy_548;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                              (nb095_alpha_dummy_551 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_551;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                              unfold nb095_alpha_dummy_553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_552 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_552;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from (by
                                unfold nb095_alpha_dummy_554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_546 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_555 D R S_cls E),
                                      (nb095_alpha_dummy_556 f)),
                                    ((nb095_alpha_dummy_551 D R S_cls E),
                                      (nb095_alpha_dummy_553 f)),
                                    ((nb095_alpha_dummy_552 D R S_cls E),
                                      (nb095_alpha_dummy_554 f)),
                                    ((nb095_alpha_dummy_544 D R S_cls E),
                                      (nb095_alpha_dummy_546 f)),
                                    ((nb095_alpha_dummy_543 D R S_cls E),
                                      (nb095_alpha_dummy_545 f)),
                                    ((nb095_alpha_dummy_549 D R S_cls E),
                                      (nb095_alpha_dummy_550 f)),
                                    ((nb095_alpha_dummy_547 D R S_cls E),
                                      (nb095_alpha_dummy_548 f)),
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
                                    (nb095_alpha_dummy_551 D R S_cls E) ≠
                                      (nb095_alpha_dummy_555 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                    (by
                                      unfold nb095_alpha_dummy_556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_555 D R S_cls E),
                                      (nb095_alpha_dummy_556 f)),
                                    ((nb095_alpha_dummy_551 D R S_cls E),
                                      (nb095_alpha_dummy_553 f)),
                                    ((nb095_alpha_dummy_552 D R S_cls E),
                                      (nb095_alpha_dummy_554 f)),
                                    ((nb095_alpha_dummy_544 D R S_cls E),
                                      (nb095_alpha_dummy_546 f)),
                                    ((nb095_alpha_dummy_543 D R S_cls E),
                                      (nb095_alpha_dummy_545 f)),
                                    ((nb095_alpha_dummy_549 D R S_cls E),
                                      (nb095_alpha_dummy_550 f)),
                                    ((nb095_alpha_dummy_547 D R S_cls E),
                                      (nb095_alpha_dummy_548 f)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                        (nb095_alpha_dummy_544 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_544;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_546 f) from (by
                        unfold nb095_alpha_dummy_546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                          (nb095_alpha_dummy_543 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_545 f) from (by
                          unfold nb095_alpha_dummy_545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                            (nb095_alpha_dummy_549 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_550 f) from (by
                            unfold nb095_alpha_dummy_550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_387 D R S_cls E) ≠
                              (nb095_alpha_dummy_547 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_547;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_390 f) ≠ (nb095_alpha_dummy_548 f) from (by
                              unfold nb095_alpha_dummy_548;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_390 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_551 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                                unfold nb095_alpha_dummy_553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_552 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from
                                (by
                                  unfold nb095_alpha_dummy_554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_549 D R S_cls E), (nb095_alpha_dummy_550 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_549 D R S_cls E),
                                        (nb095_alpha_dummy_550 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_549 D R S_cls E),
                                        (nb095_alpha_dummy_550 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
noncomputable def nb095_split_alpha_0071 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_575 D R S_cls E))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_544 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_575 D R S_cls E))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_576 f))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_546 f)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_576 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_551 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                                unfold nb095_alpha_dummy_553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_552 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from
                                (by
                                  unfold nb095_alpha_dummy_554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                    (nb095_alpha_dummy_577 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_577;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0598 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_578 f) from (by
                                    unfold nb095_alpha_dummy_578;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0599 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_544 D R S_cls E) ≠
                                      (nb095_alpha_dummy_575 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_575;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0596 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_576 f) from
                                    (by
                                      unfold nb095_alpha_dummy_576;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0597 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_577 D R S_cls E),
                                        (nb095_alpha_dummy_578 f)),
                                      ((nb095_alpha_dummy_575 D R S_cls E),
                                        (nb095_alpha_dummy_576 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_573 D R S_cls E),
                                        (nb095_alpha_dummy_574 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_577 D R S_cls E),
                                        (nb095_alpha_dummy_578 f)),
                                      ((nb095_alpha_dummy_575 D R S_cls E),
                                        (nb095_alpha_dummy_576 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_573 D R S_cls E),
                                        (nb095_alpha_dummy_574 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_544 D R S_cls E) ≠
                                (nb095_alpha_dummy_551 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_553 f) from (by
                                unfold nb095_alpha_dummy_553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                  (nb095_alpha_dummy_552 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_554 f) from
                                (by
                                  unfold nb095_alpha_dummy_554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_544 D R S_cls E) ≠
                                    (nb095_alpha_dummy_577 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_577;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0598 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_578 f) from (by
                                    unfold nb095_alpha_dummy_578;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0599 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_544 D R S_cls E) ≠
                                      (nb095_alpha_dummy_575 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_575;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0596 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_546 f) ≠ (nb095_alpha_dummy_576 f) from
                                    (by
                                      unfold nb095_alpha_dummy_576;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0597 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_558 D R S_cls E) from (by
          unfold nb095_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_561 f) from (by
          unfold nb095_alpha_dummy_561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_551 D R S_cls E) ≠ (nb095_alpha_dummy_557 D R S_cls E) from (by
          unfold nb095_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_560 f) from (by
          unfold nb095_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
          unfold nb095_alpha_dummy_555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from (by
          unfold nb095_alpha_dummy_556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_558
        D R S_cls E) ≠ (nb095_alpha_dummy_565 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠ (nb095_alpha_dummy_565
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_566 f) from (by
          unfold
            nb095_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_563 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_564 f) from (by
          unfold
            nb095_alpha_dummy_564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_559 D R S_cls E), (nb095_alpha_dummy_562 f)),
        ((nb095_alpha_dummy_558 D R S_cls E), (nb095_alpha_dummy_561 f)),
        ((nb095_alpha_dummy_557 D R S_cls E), (nb095_alpha_dummy_560 f)),
        ((nb095_alpha_dummy_555 D R S_cls E), (nb095_alpha_dummy_556 f)),
        ((nb095_alpha_dummy_551 D R S_cls E), (nb095_alpha_dummy_553 f)),
        ((nb095_alpha_dummy_552 D R S_cls E), (nb095_alpha_dummy_554 f)),
        ((nb095_alpha_dummy_577 D R S_cls E), (nb095_alpha_dummy_578 f)),
        ((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
        ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
        ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
        ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
        ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_551 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠ (nb095_alpha_dummy_569
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_570 f) from (by
          unfold
            nb095_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_558 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_561 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_551
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_553 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_559
        D R S_cls E) ≠ (nb095_alpha_dummy_571 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_572 f) from (by
          unfold
            nb095_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_559 D R S_cls E) ≠
        (nb095_alpha_dummy_567 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_562 f) ≠ (nb095_alpha_dummy_568 f) from (by
          unfold
            nb095_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_577 D R S_cls E),
                                        (nb095_alpha_dummy_578 f)),
                                      ((nb095_alpha_dummy_575 D R S_cls E),
                                        (nb095_alpha_dummy_576 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_573 D R S_cls E),
                                        (nb095_alpha_dummy_574 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
                                      (nb095_alpha_dummy_551 D R S_cls E) ≠
                                        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_553 f) ≠ (nb095_alpha_dummy_556 f) from
                                      (by
                                        unfold nb095_alpha_dummy_556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_551 D R S_cls E) ≠
        (nb095_alpha_dummy_555 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_553 f) ≠
        (nb095_alpha_dummy_556 f) from (by
                                          unfold nb095_alpha_dummy_556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_555 D R S_cls E),
                                        (nb095_alpha_dummy_556 f)),
                                      ((nb095_alpha_dummy_551 D R S_cls E),
                                        (nb095_alpha_dummy_553 f)),
                                      ((nb095_alpha_dummy_552 D R S_cls E),
                                        (nb095_alpha_dummy_554 f)),
                                      ((nb095_alpha_dummy_577 D R S_cls E),
                                        (nb095_alpha_dummy_578 f)),
                                      ((nb095_alpha_dummy_575 D R S_cls E),
                                        (nb095_alpha_dummy_576 f)),
                                      ((nb095_alpha_dummy_544 D R S_cls E),
                                        (nb095_alpha_dummy_546 f)),
                                      ((nb095_alpha_dummy_543 D R S_cls E),
                                        (nb095_alpha_dummy_545 f)),
                                      ((nb095_alpha_dummy_573 D R S_cls E),
                                        (nb095_alpha_dummy_574 f)),
                                      ((nb095_alpha_dummy_547 D R S_cls E),
                                        (nb095_alpha_dummy_548 f)),
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
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
          [((nb095_alpha_dummy_575 D R S_cls E), (nb095_alpha_dummy_576 f)),
            ((nb095_alpha_dummy_544 D R S_cls E), (nb095_alpha_dummy_546 f)),
            ((nb095_alpha_dummy_543 D R S_cls E), (nb095_alpha_dummy_545 f)),
            ((nb095_alpha_dummy_573 D R S_cls E), (nb095_alpha_dummy_574 f)),
            ((nb095_alpha_dummy_547 D R S_cls E), (nb095_alpha_dummy_548 f)),
            ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
            ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
            ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
            ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
            ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
            ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

@[expose]
noncomputable def nb095_split_alpha_0072 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_103 D R S_cls E), (nb095_alpha_dummy_104 f)),
        ((nb095_alpha_dummy_101 D R S_cls E), (nb095_alpha_dummy_102 f)),
        ((nb095_alpha_dummy_092 D R S_cls E), (nb095_alpha_dummy_094 f)),
        ((nb095_alpha_dummy_091 D R S_cls E), (nb095_alpha_dummy_093 f)),
        ((nb095_alpha_dummy_095 D R S_cls E), (nb095_alpha_dummy_096 f)),
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
