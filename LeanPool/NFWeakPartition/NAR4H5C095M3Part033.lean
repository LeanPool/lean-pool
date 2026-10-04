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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0070`. -/
@[expose]
noncomputable def nb095SplitAlpha0070 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy549 D R S_cls E))
          (Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy549 D R S_cls E))
            (Class.cab (nb095AlphaDummy543 D R S_cls E)
              (synWrex (nb095AlphaDummy544 D R S_cls E)
                (Class.cv (nb095AlphaDummy387 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy550 f))
          (Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy550 f))
            (Class.cab (nb095AlphaDummy545 f)
              (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                  (synCphi (Class.cv (nb095AlphaDummy546 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                      (nb095AlphaDummy544 D R S_cls E) from (by
                      unfold nb095AlphaDummy544;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                  (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
                      unfold nb095AlphaDummy546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0564 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                        (nb095AlphaDummy543 D R S_cls E) from (by
                        unfold nb095AlphaDummy543;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 0))))
                    (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
                        unfold nb095AlphaDummy545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy387 D R S_cls E) ≠
                          (nb095AlphaDummy549 D R S_cls E) from (by
                          unfold nb095AlphaDummy549;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy550 f) from (by
                          unfold nb095AlphaDummy550;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                            (nb095AlphaDummy547 D R S_cls E) from (by
                            unfold nb095AlphaDummy547;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy548 f) from (by
                            unfold nb095AlphaDummy548;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy390 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                              (nb095AlphaDummy551 D R S_cls E) from (by
                              unfold nb095AlphaDummy551;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0568 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                              unfold nb095AlphaDummy553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy552 D R S_cls E) from (by
                                unfold nb095AlphaDummy552;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 1))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from (by
                                unfold nb095AlphaDummy554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy546 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy555 D R S_cls E),
                                      (nb095AlphaDummy556 f)),
                                    ((nb095AlphaDummy551 D R S_cls E),
                                      (nb095AlphaDummy553 f)),
                                    ((nb095AlphaDummy552 D R S_cls E),
                                      (nb095AlphaDummy554 f)),
                                    ((nb095AlphaDummy544 D R S_cls E),
                                      (nb095AlphaDummy546 f)),
                                    ((nb095AlphaDummy543 D R S_cls E),
                                      (nb095AlphaDummy545 f)),
                                    ((nb095AlphaDummy549 D R S_cls E),
                                      (nb095AlphaDummy550 f)),
                                    ((nb095AlphaDummy547 D R S_cls E),
                                      (nb095AlphaDummy548 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy551 D R S_cls E) ≠
                                      (nb095AlphaDummy555 D R S_cls E) from (by
                                      unfold nb095AlphaDummy555;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                    (by
                                      unfold nb095AlphaDummy556;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0571 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy555 D R S_cls E),
                                      (nb095AlphaDummy556 f)),
                                    ((nb095AlphaDummy551 D R S_cls E),
                                      (nb095AlphaDummy553 f)),
                                    ((nb095AlphaDummy552 D R S_cls E),
                                      (nb095AlphaDummy554 f)),
                                    ((nb095AlphaDummy544 D R S_cls E),
                                      (nb095AlphaDummy546 f)),
                                    ((nb095AlphaDummy543 D R S_cls E),
                                      (nb095AlphaDummy545 f)),
                                    ((nb095AlphaDummy549 D R S_cls E),
                                      (nb095AlphaDummy550 f)),
                                    ((nb095AlphaDummy547 D R S_cls E),
                                      (nb095AlphaDummy548 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                        (nb095AlphaDummy544 D R S_cls E) from (by
                        unfold nb095AlphaDummy544;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E) 1))))
                    (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy546 f) from (by
                        unfold nb095AlphaDummy546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0564 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy387 D R S_cls E) ≠
                          (nb095AlphaDummy543 D R S_cls E) from (by
                          unfold nb095AlphaDummy543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0562 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy545 f) from (by
                          unfold nb095AlphaDummy545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0564 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                            (nb095AlphaDummy549 D R S_cls E) from (by
                            unfold nb095AlphaDummy549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0566 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy550 f) from (by
                            unfold nb095AlphaDummy550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0567 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy387 D R S_cls E) ≠
                              (nb095AlphaDummy547 D R S_cls E) from (by
                              unfold nb095AlphaDummy547;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0563 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy390 f) ≠ (nb095AlphaDummy548 f) from (by
                              unfold nb095AlphaDummy548;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0565 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy387 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy390 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy551 D R S_cls E) from (by
                                unfold nb095AlphaDummy551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                                unfold nb095AlphaDummy553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy552 D R S_cls E) from (by
                                  unfold nb095AlphaDummy552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from
                                (by
                                  unfold nb095AlphaDummy554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy549 D R S_cls E), (nb095AlphaDummy550 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy549 D R S_cls E),
                                        (nb095AlphaDummy550 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy549 D R S_cls E),
                                        (nb095AlphaDummy550 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0071`. -/
@[expose]
noncomputable def nb095SplitAlpha0071 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy575 D R S_cls E))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy575 D R S_cls E))
            (synCcompl (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb095AlphaDummy576 f))
            (synCcompl (synCphi (Class.cv (nb095AlphaDummy546 f)))))
          (Wff.classMem (Class.cv (nb095AlphaDummy576 f))
            (synCcompl (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy551 D R S_cls E) from (by
                                unfold nb095AlphaDummy551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                                unfold nb095AlphaDummy553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy552 D R S_cls E) from (by
                                  unfold nb095AlphaDummy552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from
                                (by
                                  unfold nb095AlphaDummy554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                    (nb095AlphaDummy577 D R S_cls E) from (by
                                    unfold nb095AlphaDummy577;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0598 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy578 f) from (by
                                    unfold nb095AlphaDummy578;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0599 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy544 D R S_cls E) ≠
                                      (nb095AlphaDummy575 D R S_cls E) from (by
                                      unfold nb095AlphaDummy575;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0596 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy576 f) from
                                    (by
                                      unfold nb095AlphaDummy576;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0597 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy577 D R S_cls E),
                                        (nb095AlphaDummy578 f)),
                                      ((nb095AlphaDummy575 D R S_cls E),
                                        (nb095AlphaDummy576 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy573 D R S_cls E),
                                        (nb095AlphaDummy574 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy577 D R S_cls E),
                                        (nb095AlphaDummy578 f)),
                                      ((nb095AlphaDummy575 D R S_cls E),
                                        (nb095AlphaDummy576 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy573 D R S_cls E),
                                        (nb095AlphaDummy574 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy544 D R S_cls E) ≠
                                (nb095AlphaDummy551 D R S_cls E) from (by
                                unfold nb095AlphaDummy551;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0568 D R S_cls E) 0))))
                            (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy553 f) from (by
                                unfold nb095AlphaDummy553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0569 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                  (nb095AlphaDummy552 D R S_cls E) from (by
                                  unfold nb095AlphaDummy552;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0568 D R S_cls E) 1))))
                              (show (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy554 f) from
                                (by
                                  unfold nb095AlphaDummy554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0569 f) 1))))
                              (TAlphaVar.there (show (nb095AlphaDummy544 D R S_cls E) ≠
                                    (nb095AlphaDummy577 D R S_cls E) from (by
                                    unfold nb095AlphaDummy577;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0598 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy578 f) from (by
                                    unfold nb095AlphaDummy578;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0599 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095AlphaDummy544 D R S_cls E) ≠
                                      (nb095AlphaDummy575 D R S_cls E) from (by
                                      unfold nb095AlphaDummy575;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0596 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy546 f) ≠ (nb095AlphaDummy576 f) from
                                    (by
                                      unfold nb095AlphaDummy576;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0597 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy544 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy546 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy558 D R S_cls E) from (by
          unfold nb095AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy561 f) from (by
          unfold nb095AlphaDummy561;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy551 D R S_cls E) ≠ (nb095AlphaDummy557 D R S_cls E) from (by
          unfold nb095AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0572 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy560 f) from (by
          unfold nb095AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0573 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
          unfold nb095AlphaDummy555;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0570 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from (by
          unfold nb095AlphaDummy556;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0571 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy558
        D R S_cls E) ≠ (nb095AlphaDummy565 D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0576
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0577
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0574
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0575
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠ (nb095AlphaDummy565
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0580
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy566 f) from (by
          unfold
            nb095AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0581
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy563 D R S_cls E) from (by
          unfold
            nb095AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0578
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy564 f) from (by
          unfold
            nb095AlphaDummy564;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0579
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy559 D R S_cls E), (nb095AlphaDummy562 f)),
        ((nb095AlphaDummy558 D R S_cls E), (nb095AlphaDummy561 f)),
        ((nb095AlphaDummy557 D R S_cls E), (nb095AlphaDummy560 f)),
        ((nb095AlphaDummy555 D R S_cls E), (nb095AlphaDummy556 f)),
        ((nb095AlphaDummy551 D R S_cls E), (nb095AlphaDummy553 f)),
        ((nb095AlphaDummy552 D R S_cls E), (nb095AlphaDummy554 f)),
        ((nb095AlphaDummy577 D R S_cls E), (nb095AlphaDummy578 f)),
        ((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
        ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
        ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
        ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
        ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy551 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠ (nb095AlphaDummy569
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0584
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy570 f) from (by
          unfold
            nb095AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0585
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy558 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0582
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy561 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0583
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy551
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy553 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy559
        D R S_cls E) ≠ (nb095AlphaDummy571 D R S_cls E) from (by
          unfold
            nb095AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0588
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy572 f) from (by
          unfold
            nb095AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0589
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy559 D R S_cls E) ≠
        (nb095AlphaDummy567 D R S_cls E) from (by
          unfold
            nb095AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0586
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy562 f) ≠ (nb095AlphaDummy568 f) from (by
          unfold
            nb095AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0587
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy577 D R S_cls E),
                                        (nb095AlphaDummy578 f)),
                                      ((nb095AlphaDummy575 D R S_cls E),
                                        (nb095AlphaDummy576 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy573 D R S_cls E),
                                        (nb095AlphaDummy574 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy551 D R S_cls E) ≠
                                        (nb095AlphaDummy555 D R S_cls E) from (by
                                        unfold nb095AlphaDummy555;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0570 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy553 f) ≠ (nb095AlphaDummy556 f) from
                                      (by
                                        unfold nb095AlphaDummy556;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0571 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy551 D R S_cls E) ≠
        (nb095AlphaDummy555 D R S_cls E) from (by
                                          unfold nb095AlphaDummy555;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0570 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy553 f) ≠
        (nb095AlphaDummy556 f) from (by
                                          unfold nb095AlphaDummy556;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0571 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy555 D R S_cls E),
                                        (nb095AlphaDummy556 f)),
                                      ((nb095AlphaDummy551 D R S_cls E),
                                        (nb095AlphaDummy553 f)),
                                      ((nb095AlphaDummy552 D R S_cls E),
                                        (nb095AlphaDummy554 f)),
                                      ((nb095AlphaDummy577 D R S_cls E),
                                        (nb095AlphaDummy578 f)),
                                      ((nb095AlphaDummy575 D R S_cls E),
                                        (nb095AlphaDummy576 f)),
                                      ((nb095AlphaDummy544 D R S_cls E),
                                        (nb095AlphaDummy546 f)),
                                      ((nb095AlphaDummy543 D R S_cls E),
                                        (nb095AlphaDummy545 f)),
                                      ((nb095AlphaDummy573 D R S_cls E),
                                        (nb095AlphaDummy574 f)),
                                      ((nb095AlphaDummy547 D R S_cls E),
                                        (nb095AlphaDummy548 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
          [((nb095AlphaDummy575 D R S_cls E), (nb095AlphaDummy576 f)),
            ((nb095AlphaDummy544 D R S_cls E), (nb095AlphaDummy546 f)),
            ((nb095AlphaDummy543 D R S_cls E), (nb095AlphaDummy545 f)),
            ((nb095AlphaDummy573 D R S_cls E), (nb095AlphaDummy574 f)),
            ((nb095AlphaDummy547 D R S_cls E), (nb095AlphaDummy548 f)),
            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
            ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
            ((nb095AlphaDummy000 D R S_cls E), f)] (synCcompl (synCsn (synC0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0072`. -/
@[expose]
noncomputable def nb095SplitAlpha0072 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
          (Class.cab (nb095AlphaDummy097 D R S_cls E)
            (synWrex (nb095AlphaDummy098 D R S_cls E)
              (Class.cv (nb095AlphaDummy091 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy103 D R S_cls E))
            (Class.cab (nb095AlphaDummy097 D R S_cls E)
              (synWrex (nb095AlphaDummy098 D R S_cls E)
                (Class.cv (nb095AlphaDummy091 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy097 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy098 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
          (Class.cab (nb095AlphaDummy099 f)
            (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                (synCphi (Class.cv (nb095AlphaDummy100 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy104 f))
            (Class.cab (nb095AlphaDummy099 f)
              (synWrex (nb095AlphaDummy100 f) (Class.cv (nb095AlphaDummy093 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy099 f))
                  (synCphi (Class.cv (nb095AlphaDummy100 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                      (nb095AlphaDummy098 D R S_cls E) from (by
                      unfold nb095AlphaDummy098;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                  (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                      unfold nb095AlphaDummy100;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0086 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy097 D R S_cls E) from (by
                        unfold nb095AlphaDummy097;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 0))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                        unfold nb095AlphaDummy099;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy103 D R S_cls E) from (by
                          unfold nb095AlphaDummy103;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                          unfold nb095AlphaDummy104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy101 D R S_cls E) from (by
                            unfold nb095AlphaDummy101;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                            unfold nb095AlphaDummy102;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                              (nb095AlphaDummy105 D R S_cls E) from (by
                              unfold nb095AlphaDummy105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0090 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                              unfold nb095AlphaDummy107;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy106 D R S_cls E) from (by
                                unfold nb095AlphaDummy106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 1))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from (by
                                unfold nb095AlphaDummy108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy105 D R S_cls E) ≠
                                      (nb095AlphaDummy109 D R S_cls E) from (by
                                      unfold nb095AlphaDummy109;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                    (by
                                      unfold nb095AlphaDummy110;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0093 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy109 D R S_cls E),
                                      (nb095AlphaDummy110 f)),
                                    ((nb095AlphaDummy105 D R S_cls E),
                                      (nb095AlphaDummy107 f)),
                                    ((nb095AlphaDummy106 D R S_cls E),
                                      (nb095AlphaDummy108 f)),
                                    ((nb095AlphaDummy098 D R S_cls E),
                                      (nb095AlphaDummy100 f)),
                                    ((nb095AlphaDummy097 D R S_cls E),
                                      (nb095AlphaDummy099 f)),
                                    ((nb095AlphaDummy103 D R S_cls E),
                                      (nb095AlphaDummy104 f)),
                                    ((nb095AlphaDummy101 D R S_cls E),
                                      (nb095AlphaDummy102 f)),
                                    ((nb095AlphaDummy092 D R S_cls E),
                                      (nb095AlphaDummy094 f)),
                                    ((nb095AlphaDummy091 D R S_cls E),
                                      (nb095AlphaDummy093 f)),
                                    ((nb095AlphaDummy095 D R S_cls E),
                                      (nb095AlphaDummy096 f)),
                                    ((nb095AlphaDummy387 D R S_cls E),
                                      (nb095AlphaDummy390 f)),
                                    ((nb095AlphaDummy386 D R S_cls E),
                                      (nb095AlphaDummy389 f)),
                                    ((nb095AlphaDummy385 D R S_cls E),
                                      (nb095AlphaDummy388 f)),
                                    ((nb095AlphaDummy391 D R S_cls E),
                                      (nb095AlphaDummy392 f)),
                                    ((nb095AlphaDummy001 D R S_cls E), u),
                                    ((nb095AlphaDummy002 D R S_cls E), x),
                                    ((nb095AlphaDummy000 D R S_cls E), f)]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                        (nb095AlphaDummy098 D R S_cls E) from (by
                        unfold nb095AlphaDummy098;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E) 1))))
                    (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy100 f) from (by
                        unfold nb095AlphaDummy100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0086 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy091 D R S_cls E) ≠
                          (nb095AlphaDummy097 D R S_cls E) from (by
                          unfold nb095AlphaDummy097;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0084 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy099 f) from (by
                          unfold nb095AlphaDummy099;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0086 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                            (nb095AlphaDummy103 D R S_cls E) from (by
                            unfold nb095AlphaDummy103;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0088 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy104 f) from (by
                            unfold nb095AlphaDummy104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0089 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy091 D R S_cls E) ≠
                              (nb095AlphaDummy101 D R S_cls E) from (by
                              unfold nb095AlphaDummy101;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0085 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy093 f) ≠ (nb095AlphaDummy102 f) from (by
                              unfold nb095AlphaDummy102;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0087 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (by decide))
                            (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy094 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy098 D R S_cls E) ≠
                                (nb095AlphaDummy105 D R S_cls E) from (by
                                unfold nb095AlphaDummy105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0090 D R S_cls E) 0))))
                            (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy107 f) from (by
                                unfold nb095AlphaDummy107;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0091 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy098 D R S_cls E) ≠
                                  (nb095AlphaDummy106 D R S_cls E) from (by
                                  unfold nb095AlphaDummy106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0090 D R S_cls E) 1))))
                              (show (nb095AlphaDummy100 f) ≠ (nb095AlphaDummy108 f) from
                                (by
                                  unfold nb095AlphaDummy108;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0091 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy100 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy112 D R S_cls E) from (by
          unfold nb095AlphaDummy112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy115 f) from (by
          unfold nb095AlphaDummy115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy111 D R S_cls E) from (by
          unfold nb095AlphaDummy111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0094 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy114 f) from (by
          unfold nb095AlphaDummy114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0095 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
          unfold nb095AlphaDummy109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0092 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from (by
          unfold nb095AlphaDummy110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0093 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy112
        D R S_cls E) ≠ (nb095AlphaDummy119 D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0098
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0099
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0096
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0097
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠ (nb095AlphaDummy119
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0102
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy120 f) from (by
          unfold
            nb095AlphaDummy120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0103
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy117 D R S_cls E) from (by
          unfold
            nb095AlphaDummy117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0100
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy118 f) from (by
          unfold
            nb095AlphaDummy118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0101
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy113 D R S_cls E), (nb095AlphaDummy116 f)),
        ((nb095AlphaDummy112 D R S_cls E), (nb095AlphaDummy115 f)),
        ((nb095AlphaDummy111 D R S_cls E), (nb095AlphaDummy114 f)),
        ((nb095AlphaDummy109 D R S_cls E), (nb095AlphaDummy110 f)),
        ((nb095AlphaDummy105 D R S_cls E), (nb095AlphaDummy107 f)),
        ((nb095AlphaDummy106 D R S_cls E), (nb095AlphaDummy108 f)),
        ((nb095AlphaDummy098 D R S_cls E), (nb095AlphaDummy100 f)),
        ((nb095AlphaDummy097 D R S_cls E), (nb095AlphaDummy099 f)),
        ((nb095AlphaDummy103 D R S_cls E), (nb095AlphaDummy104 f)),
        ((nb095AlphaDummy101 D R S_cls E), (nb095AlphaDummy102 f)),
        ((nb095AlphaDummy092 D R S_cls E), (nb095AlphaDummy094 f)),
        ((nb095AlphaDummy091 D R S_cls E), (nb095AlphaDummy093 f)),
        ((nb095AlphaDummy095 D R S_cls E), (nb095AlphaDummy096 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy123
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0106
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy124 f) from (by
          unfold
            nb095AlphaDummy124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0107
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy112 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0104
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0105
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy105
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy113
        D R S_cls E) ≠ (nb095AlphaDummy125 D R S_cls E) from (by
          unfold
            nb095AlphaDummy125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0110
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy126 f) from (by
          unfold
            nb095AlphaDummy126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0111
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy113 D R S_cls E) ≠
        (nb095AlphaDummy121 D R S_cls E) from (by
          unfold
            nb095AlphaDummy121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0108
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy116 f) ≠ (nb095AlphaDummy122 f) from (by
          unfold
            nb095AlphaDummy122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0109
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy105 D R S_cls E) ≠
                                        (nb095AlphaDummy109 D R S_cls E) from (by
                                        unfold nb095AlphaDummy109;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0092 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy110 f) from
                                      (by
                                        unfold nb095AlphaDummy110;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0093 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy105 D R S_cls E) ≠
        (nb095AlphaDummy109 D R S_cls E) from (by
                                          unfold nb095AlphaDummy109;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0092 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy107 f) ≠
        (nb095AlphaDummy110 f) from (by
                                          unfold nb095AlphaDummy110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0093 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy109 D R S_cls E),
                                        (nb095AlphaDummy110 f)),
                                      ((nb095AlphaDummy105 D R S_cls E),
                                        (nb095AlphaDummy107 f)),
                                      ((nb095AlphaDummy106 D R S_cls E),
                                        (nb095AlphaDummy108 f)),
                                      ((nb095AlphaDummy098 D R S_cls E),
                                        (nb095AlphaDummy100 f)),
                                      ((nb095AlphaDummy097 D R S_cls E),
                                        (nb095AlphaDummy099 f)),
                                      ((nb095AlphaDummy103 D R S_cls E),
                                        (nb095AlphaDummy104 f)),
                                      ((nb095AlphaDummy101 D R S_cls E),
                                        (nb095AlphaDummy102 f)),
                                      ((nb095AlphaDummy092 D R S_cls E),
                                        (nb095AlphaDummy094 f)),
                                      ((nb095AlphaDummy091 D R S_cls E),
                                        (nb095AlphaDummy093 f)),
                                      ((nb095AlphaDummy095 D R S_cls E),
                                        (nb095AlphaDummy096 f)),
                                      ((nb095AlphaDummy387 D R S_cls E),
                                        (nb095AlphaDummy390 f)),
                                      ((nb095AlphaDummy386 D R S_cls E),
                                        (nb095AlphaDummy389 f)),
                                      ((nb095AlphaDummy385 D R S_cls E),
                                        (nb095AlphaDummy388 f)),
                                      ((nb095AlphaDummy391 D R S_cls E),
                                        (nb095AlphaDummy392 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
