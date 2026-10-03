/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block022

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part066`. -/


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
noncomputable def nb090_split_alpha_0044 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_551 A))
          (Class.cab (nb090_alpha_dummy_545 A)
            (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_551 A))
            (Class.cab (nb090_alpha_dummy_545 A)
              (syn_wrex (nb090_alpha_dummy_546 A) (Class.cv (nb090_alpha_dummy_504 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_545 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_552 h))
          (Class.cab (nb090_alpha_dummy_547 h)
            (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_552 h))
            (Class.cab (nb090_alpha_dummy_547 h)
              (syn_wrex (nb090_alpha_dummy_548 h) (Class.cv (nb090_alpha_dummy_506 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_547 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_548 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_546 A) from (by
                      unfold nb090_alpha_dummy_546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
                  (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_548 h) from (by
                      unfold nb090_alpha_dummy_548;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_545 A) from (by
                        unfold nb090_alpha_dummy_545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
                    (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_547 h) from (by
                        unfold nb090_alpha_dummy_547;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0556 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_551 A) from (by
                          unfold nb090_alpha_dummy_551;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0558 A) 0))))
                      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_552 h) from (by
                          unfold nb090_alpha_dummy_552;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0559 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_549 A) from (by
                            unfold nb090_alpha_dummy_549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0555 A) 0))))
                        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_550 h) from (by
                            unfold nb090_alpha_dummy_550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0557 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_553 A) from (by
                              unfold nb090_alpha_dummy_553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                          (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_555 h) from (by
                              unfold nb090_alpha_dummy_555;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_554 A) from (by
                                unfold nb090_alpha_dummy_554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                            (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_556 h) from (by
                                unfold nb090_alpha_dummy_556;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_546 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_548 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_560 A) from (by
          unfold nb090_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 1)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_563 h) from (by
          unfold nb090_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_559 A) from (by
          unfold nb090_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 0)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_562 h) from (by
          unfold nb090_alpha_dummy_562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
          unfold nb090_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A)
                  0)))) (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
          unfold nb090_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A),
        (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A),
        (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A),
        (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A),
        (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A),
        (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A),
        (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_560
        A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561
        A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561
        A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                      (by
                                        unfold nb090_alpha_dummy_557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090_alpha_dummy_555 h) ≠
                                        (nb090_alpha_dummy_558 h) from (by
                                        unfold nb090_alpha_dummy_558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                                    ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                                    ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                                    ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                                    ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                                    ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
                                    ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                                    (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                    (by
                                      unfold nb090_alpha_dummy_557;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0562 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from
                                    (by
                                      unfold nb090_alpha_dummy_558;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0563 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                      (by
                                        unfold nb090_alpha_dummy_557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090_alpha_dummy_555 h) ≠
                                        (nb090_alpha_dummy_558 h) from (by
                                        unfold nb090_alpha_dummy_558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                                    ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                                    ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                                    ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                                    ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                                    ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
                                    ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                    (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_546 A) from (by
                        unfold nb090_alpha_dummy_546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
                    (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_548 h) from (by
                        unfold nb090_alpha_dummy_548;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0556 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_545 A) from (by
                          unfold nb090_alpha_dummy_545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
                      (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_547 h) from (by
                          unfold nb090_alpha_dummy_547;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_551 A) from (by
                            unfold nb090_alpha_dummy_551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0558 A) 0))))
                        (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_552 h) from (by
                            unfold nb090_alpha_dummy_552;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0559 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_504 A) ≠ (nb090_alpha_dummy_549 A) from (by
                              unfold nb090_alpha_dummy_549;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0555 A) 0))))
                          (show (nb090_alpha_dummy_506 h) ≠ (nb090_alpha_dummy_550 h) from (by
                              unfold nb090_alpha_dummy_550;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0557 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_504 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_503 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_506 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_505 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_553 A) from (by
                                unfold nb090_alpha_dummy_553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                            (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_555 h) from (by
                                unfold nb090_alpha_dummy_555;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_554 A) from
                                (by
                                  unfold nb090_alpha_dummy_554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                              (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_556 h) from
                                (by
                                  unfold nb090_alpha_dummy_556;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_546 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_548 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_560 A) from (by
          unfold nb090_alpha_dummy_560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 1)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_563 h) from (by
          unfold nb090_alpha_dummy_563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_559 A) from (by
          unfold nb090_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A)
                  0)))) (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_562 h) from (by
          unfold nb090_alpha_dummy_562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_553 A) ≠
        (nb090_alpha_dummy_557 A) from (by
          unfold nb090_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A)
                  0)))) (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
          unfold nb090_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A),
        (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A),
        (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A),
        (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A),
        (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A),
        (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A),
        (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_555
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_560
        A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561
        A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561
        A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A)
                                        from (by
                                          unfold nb090_alpha_dummy_557;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0562 A) 0)))) (show
                                        (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h)
                                        from (by
                                          unfold nb090_alpha_dummy_558;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0563 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                                      ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                                      ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                                      ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                                      ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                                      ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
                                      ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                                      (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                      (by
                                        unfold nb090_alpha_dummy_557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090_alpha_dummy_555 h) ≠
                                        (nb090_alpha_dummy_558 h) from (by
                                        unfold nb090_alpha_dummy_558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A)
                                        from (by
                                          unfold nb090_alpha_dummy_557;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0562 A) 0)))) (show
                                        (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h)
                                        from (by
                                          unfold nb090_alpha_dummy_558;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0563 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                                      ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                                      ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                                      ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                                      ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                                      ((nb090_alpha_dummy_551 A), (nb090_alpha_dummy_552 h)),
                                      ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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

/-! Certificates from `NAR4C090C001Part067`. -/


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
noncomputable def nb090_split_alpha_0045 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
        ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
        ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
        ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_579 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_546 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_579 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_546 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_580 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_580 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_548 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_553 A) from (by
                      unfold nb090_alpha_dummy_553;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                  (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_555 h) from (by
                      unfold nb090_alpha_dummy_555;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_554 A) from (by
                        unfold nb090_alpha_dummy_554;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                    (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_556 h) from (by
                        unfold nb090_alpha_dummy_556;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0561 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_579 A) from (by
                          unfold nb090_alpha_dummy_579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0590 A) 0))))
                      (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_580 h) from (by
                          unfold nb090_alpha_dummy_580;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0591 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_577 A) from (by
                            unfold nb090_alpha_dummy_577;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0588 A) 0))))
                        (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_578 h) from (by
                            unfold nb090_alpha_dummy_578;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0589 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_546 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_548 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_560 A) from
                                      (by
                                        unfold nb090_alpha_dummy_560;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0564 A)
                                                1)))) (show (nb090_alpha_dummy_555 h) ≠
                                        (nb090_alpha_dummy_563 h) from (by
                                        unfold nb090_alpha_dummy_563;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0565 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_559 A)
                                        from (by
                                          unfold nb090_alpha_dummy_559;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0564 A) 0)))) (show
                                        (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_562 h)
                                        from (by
                                          unfold nb090_alpha_dummy_562;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0565 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_553 A) ≠
        (nb090_alpha_dummy_557 A) from (by
          unfold nb090_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A) 0)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_558 h) from (by
          unfold nb090_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_561 A),
        (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)),
                                        ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
                                        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                                        ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                                        ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                                        ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
                                        ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
                                        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                                        ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                                        ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
                                        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                                        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)),
        ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A),
        (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
        ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A),
        (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
        ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A),
        (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
        ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A),
        (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A),
        (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A),
        (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A),
        (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
                                unfold nb090_alpha_dummy_557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
                                unfold nb090_alpha_dummy_558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                            ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                            ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                            ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
                            ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
                            ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                            ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                            ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
                            ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                            ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                            ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                            ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
                              unfold nb090_alpha_dummy_557;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                          (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
                              unfold nb090_alpha_dummy_558;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
                                unfold nb090_alpha_dummy_557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
                                unfold nb090_alpha_dummy_558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                            ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                            ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                            ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
                            ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
                            ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                            ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                            ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
                            ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                            ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                            ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                            ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                            ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                            ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                            ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                            ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                            ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                            ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_553 A) from (by
                        unfold nb090_alpha_dummy_553;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                    (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_555 h) from (by
                        unfold nb090_alpha_dummy_555;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0561 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_554 A) from (by
                          unfold nb090_alpha_dummy_554;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                      (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_556 h) from (by
                          unfold nb090_alpha_dummy_556;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_579 A) from (by
                            unfold nb090_alpha_dummy_579;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0590 A) 0))))
                        (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_580 h) from (by
                            unfold nb090_alpha_dummy_580;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0591 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_546 A) ≠ (nb090_alpha_dummy_577 A) from (by
                              unfold nb090_alpha_dummy_577;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0588 A) 0))))
                          (show (nb090_alpha_dummy_548 h) ≠ (nb090_alpha_dummy_578 h) from (by
                              unfold nb090_alpha_dummy_578;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0589 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_546 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_548 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_553 A) ≠
        (nb090_alpha_dummy_560 A) from (by
                                          unfold nb090_alpha_dummy_560;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0564 A) 1)))) (show
                                        (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_563 h)
                                        from (by
                                          unfold nb090_alpha_dummy_563;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0565 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_553 A) ≠
        (nb090_alpha_dummy_559 A) from (by
          unfold nb090_alpha_dummy_559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 0)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_562 h) from (by
          unfold nb090_alpha_dummy_562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
          unfold nb090_alpha_dummy_557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A) 0)))) (show (nb090_alpha_dummy_555 h) ≠
        (nb090_alpha_dummy_558 h) from (by
          unfold nb090_alpha_dummy_558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_561 A),
        (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A), (nb090_alpha_dummy_563 h)),
        ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)), ((nb090_alpha_dummy_557 A),
        (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
        ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)), ((nb090_alpha_dummy_579 A),
        (nb090_alpha_dummy_580 h)), ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
        ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)), ((nb090_alpha_dummy_545 A),
        (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
        ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_567 A) from (by
          unfold
            nb090_alpha_dummy_567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_568 h) from (by
          unfold
            nb090_alpha_dummy_568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_565 A) from (by
          unfold
            nb090_alpha_dummy_565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_566 h) from (by
          unfold
            nb090_alpha_dummy_566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_561 A), (nb090_alpha_dummy_564 h)), ((nb090_alpha_dummy_560 A),
        (nb090_alpha_dummy_563 h)), ((nb090_alpha_dummy_559 A), (nb090_alpha_dummy_562 h)),
        ((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)), ((nb090_alpha_dummy_553 A),
        (nb090_alpha_dummy_555 h)), ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
        ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)), ((nb090_alpha_dummy_577 A),
        (nb090_alpha_dummy_578 h)), ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
        ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)), ((nb090_alpha_dummy_575 A),
        (nb090_alpha_dummy_576 h)), ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A),
        (nb090_alpha_dummy_505 h)), ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A),
        (nb090_alpha_dummy_427 h)), ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A),
        (nb090_alpha_dummy_422 h)), ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_553 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠ (nb090_alpha_dummy_571 A) from (by
          unfold
            nb090_alpha_dummy_571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_572 h) from (by
          unfold
            nb090_alpha_dummy_572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_560 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090_alpha_dummy_563 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_553
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_555 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_561 A) ≠ (nb090_alpha_dummy_573 A) from (by
          unfold
            nb090_alpha_dummy_573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_574 h) from (by
          unfold
            nb090_alpha_dummy_574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_561 A) ≠
        (nb090_alpha_dummy_569 A) from (by
          unfold
            nb090_alpha_dummy_569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090_alpha_dummy_564 h) ≠ (nb090_alpha_dummy_570 h) from (by
          unfold
            nb090_alpha_dummy_570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                (by
                                  unfold nb090_alpha_dummy_557;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                              (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from
                                (by
                                  unfold nb090_alpha_dummy_558;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                              ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                              ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                              ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
                              ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
                              ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                              ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                              ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
                              ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                              ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                              ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                              ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from (by
                                unfold nb090_alpha_dummy_557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from (by
                                unfold nb090_alpha_dummy_558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_553 A) ≠ (nb090_alpha_dummy_557 A) from
                                (by
                                  unfold nb090_alpha_dummy_557;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                              (show (nb090_alpha_dummy_555 h) ≠ (nb090_alpha_dummy_558 h) from
                                (by
                                  unfold nb090_alpha_dummy_558;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_557 A), (nb090_alpha_dummy_558 h)),
                              ((nb090_alpha_dummy_553 A), (nb090_alpha_dummy_555 h)),
                              ((nb090_alpha_dummy_554 A), (nb090_alpha_dummy_556 h)),
                              ((nb090_alpha_dummy_579 A), (nb090_alpha_dummy_580 h)),
                              ((nb090_alpha_dummy_577 A), (nb090_alpha_dummy_578 h)),
                              ((nb090_alpha_dummy_546 A), (nb090_alpha_dummy_548 h)),
                              ((nb090_alpha_dummy_545 A), (nb090_alpha_dummy_547 h)),
                              ((nb090_alpha_dummy_575 A), (nb090_alpha_dummy_576 h)),
                              ((nb090_alpha_dummy_549 A), (nb090_alpha_dummy_550 h)),
                              ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                              ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                              ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
                              ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
                              ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
                              ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
                              ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
                              ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
                              ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part068`. -/


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
noncomputable def nb090_split_alpha_0046 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
        ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
        ((nb090_alpha_dummy_425 A), (nb090_alpha_dummy_428 h)),
        ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)),
        ((nb090_alpha_dummy_429 A), (nb090_alpha_dummy_430 h)),
        ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
          (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
          (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                      unfold nb090_alpha_dummy_136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                      unfold nb090_alpha_dummy_138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                        unfold nb090_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                        unfold nb090_alpha_dummy_137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                          unfold nb090_alpha_dummy_141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                          unfold nb090_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                            unfold nb090_alpha_dummy_139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                            unfold nb090_alpha_dummy_140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                              unfold nb090_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                              unfold nb090_alpha_dummy_145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                                unfold nb090_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                                unfold nb090_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                    ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                    ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                        unfold nb090_alpha_dummy_136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                        unfold nb090_alpha_dummy_138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                          unfold nb090_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                          unfold nb090_alpha_dummy_137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                            unfold nb090_alpha_dummy_141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                            unfold nb090_alpha_dummy_142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                              unfold nb090_alpha_dummy_139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                              unfold nb090_alpha_dummy_140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                                unfold nb090_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                                unfold nb090_alpha_dummy_145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from
                                (by
                                  unfold nb090_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from
                                (by
                                  unfold nb090_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
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
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_504 A),
        (nb090_alpha_dummy_506 h)), ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
        ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)), ((nb090_alpha_dummy_425 A),
        (nb090_alpha_dummy_428 h)), ((nb090_alpha_dummy_424 A), (nb090_alpha_dummy_427 h)),
        ((nb090_alpha_dummy_423 A), (nb090_alpha_dummy_426 h)), ((nb090_alpha_dummy_429 A),
        (nb090_alpha_dummy_430 h)), ((nb090_alpha_dummy_421 A), (nb090_alpha_dummy_422 h)),
        ((nb090_alpha_dummy_419 A), (nb090_alpha_dummy_420 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_504 A), (nb090_alpha_dummy_506 h)),
                                      ((nb090_alpha_dummy_503 A), (nb090_alpha_dummy_505 h)),
                                      ((nb090_alpha_dummy_507 A), (nb090_alpha_dummy_508 h)),
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
