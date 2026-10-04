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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0044`. -/
@[expose]
noncomputable def nb090SplitAlpha0044 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy551 A))
          (Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy551 A))
            (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCphi (Class.cv (nb090AlphaDummy546 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy552 h))
          (Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy552 h))
            (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCphi (Class.cv (nb090AlphaDummy548 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy546 A) from (by
                      unfold nb090AlphaDummy546;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
                  (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy548 h) from (by
                      unfold nb090AlphaDummy548;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy545 A) from (by
                        unfold nb090AlphaDummy545;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
                    (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy547 h) from (by
                        unfold nb090AlphaDummy547;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0556 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy551 A) from (by
                          unfold nb090AlphaDummy551;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0558 A) 0))))
                      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy552 h) from (by
                          unfold nb090AlphaDummy552;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0559 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy549 A) from (by
                            unfold nb090AlphaDummy549;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0555 A) 0))))
                        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy550 h) from (by
                            unfold nb090AlphaDummy550;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0557 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy504 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy503 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy506 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy505 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy553 A) from (by
                              unfold nb090AlphaDummy553;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                          (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy555 h) from (by
                              unfold nb090AlphaDummy555;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy554 A) from (by
                                unfold nb090AlphaDummy554;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                            (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy556 h) from (by
                                unfold nb090AlphaDummy556;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy546 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy548 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy560 A) from (by
          unfold nb090AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 1)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy563 h) from (by
          unfold nb090AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy559 A) from (by
          unfold nb090AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 0)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy562 h) from (by
          unfold nb090AlphaDummy562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
          unfold nb090AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A)
                  0)))) (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
          unfold nb090AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A),
        (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A),
        (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A),
        (nb090AlphaDummy547 h)), ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A),
        (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A),
        (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A),
        (nb090AlphaDummy547 h)), ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy560
        A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561
        A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561
        A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                      (by
                                        unfold nb090AlphaDummy557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090AlphaDummy555 h) ≠
                                        (nb090AlphaDummy558 h) from (by
                                        unfold nb090AlphaDummy558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                                    ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                                    ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                                    ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                                    ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                                    ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
                                    ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                    (by
                                      unfold nb090AlphaDummy557;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0562 A)
                                              0)))) (show
                                    (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from
                                    (by
                                      unfold nb090AlphaDummy558;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0563 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                      (by
                                        unfold nb090AlphaDummy557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090AlphaDummy555 h) ≠
                                        (nb090AlphaDummy558 h) from (by
                                        unfold nb090AlphaDummy558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                                    ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                                    ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                                    ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                                    ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                                    ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
                                    ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy546 A) from (by
                        unfold nb090AlphaDummy546;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
                    (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy548 h) from (by
                        unfold nb090AlphaDummy548;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0556 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy545 A) from (by
                          unfold nb090AlphaDummy545;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
                      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy547 h) from (by
                          unfold nb090AlphaDummy547;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy551 A) from (by
                            unfold nb090AlphaDummy551;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0558 A) 0))))
                        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy552 h) from (by
                            unfold nb090AlphaDummy552;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0559 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy549 A) from (by
                              unfold nb090AlphaDummy549;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0555 A) 0))))
                          (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy550 h) from (by
                              unfold nb090AlphaDummy550;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0557 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy504 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy503 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy506 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy505 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy553 A) from (by
                                unfold nb090AlphaDummy553;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                            (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy555 h) from (by
                                unfold nb090AlphaDummy555;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy554 A) from
                                (by
                                  unfold nb090AlphaDummy554;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                              (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy556 h) from
                                (by
                                  unfold nb090AlphaDummy556;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy546 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy548 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy560 A) from (by
          unfold nb090AlphaDummy560;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 1)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy563 h) from (by
          unfold nb090AlphaDummy563;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy559 A) from (by
          unfold nb090AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A)
                  0)))) (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy562 h) from (by
          unfold nb090AlphaDummy562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy553 A) ≠
        (nb090AlphaDummy557 A) from (by
          unfold nb090AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A)
                  0)))) (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
          unfold nb090AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A),
        (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A),
        (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A),
        (nb090AlphaDummy547 h)), ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A),
        (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A),
        (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A),
        (nb090AlphaDummy547 h)), ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy555
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy560
        A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561
        A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561
        A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A)
                                        from (by
                                          unfold nb090AlphaDummy557;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0562 A) 0)))) (show
                                        (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h)
                                        from (by
                                          unfold nb090AlphaDummy558;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0563 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                                      ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                                      ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                                      ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                                      ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                                      ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
                                      ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                      (by
                                        unfold nb090AlphaDummy557;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0562 A)
                                                0)))) (show (nb090AlphaDummy555 h) ≠
                                        (nb090AlphaDummy558 h) from (by
                                        unfold nb090AlphaDummy558;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0563 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A)
                                        from (by
                                          unfold nb090AlphaDummy557;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0562 A) 0)))) (show
                                        (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h)
                                        from (by
                                          unfold nb090AlphaDummy558;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0563 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                                      ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                                      ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                                      ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                                      ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                                      ((nb090AlphaDummy551 A), (nb090AlphaDummy552 h)),
                                      ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0045`. -/
@[expose]
noncomputable def nb090SplitAlpha0045 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
        ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
        ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
        ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy579 A))
          (synCphi (Class.cv (nb090AlphaDummy546 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy579 A))
            (synCphi (Class.cv (nb090AlphaDummy546 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy580 h))
          (synCphi (Class.cv (nb090AlphaDummy548 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy580 h))
            (synCphi (Class.cv (nb090AlphaDummy548 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy553 A) from (by
                      unfold nb090AlphaDummy553;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                  (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy555 h) from (by
                      unfold nb090AlphaDummy555;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0561 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy554 A) from (by
                        unfold nb090AlphaDummy554;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                    (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy556 h) from (by
                        unfold nb090AlphaDummy556;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0561 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy579 A) from (by
                          unfold nb090AlphaDummy579;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0590 A) 0))))
                      (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy580 h) from (by
                          unfold nb090AlphaDummy580;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0591 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy577 A) from (by
                            unfold nb090AlphaDummy577;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0588 A) 0))))
                        (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy578 h) from (by
                            unfold nb090AlphaDummy578;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0589 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy546 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy548 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy560 A) from
                                      (by
                                        unfold nb090AlphaDummy560;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0564 A)
                                                1)))) (show (nb090AlphaDummy555 h) ≠
                                        (nb090AlphaDummy563 h) from (by
                                        unfold nb090AlphaDummy563;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0565 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy559 A)
                                        from (by
                                          unfold nb090AlphaDummy559;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0564 A) 0)))) (show
                                        (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy562 h)
                                        from (by
                                          unfold nb090AlphaDummy562;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0565 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy553 A) ≠
        (nb090AlphaDummy557 A) from (by
          unfold nb090AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A) 0)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy558 h) from (by
          unfold nb090AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy561 A),
        (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A), (nb090AlphaDummy563 h)),
                                        ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
                                        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                                        ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                                        ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                                        ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
                                        ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
                                        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                                        ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                                        ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
                                        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                                        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                        ((nb090AlphaDummy000 A), h),
                                        ((nb090AlphaDummy002 A), v),
                                        ((nb090AlphaDummy001 A), u),
                                        ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)),
        ((nb090AlphaDummy560 A), (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A),
        (nb090AlphaDummy562 h)), ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
        ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A),
        (nb090AlphaDummy556 h)), ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
        ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)), ((nb090AlphaDummy546 A),
        (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
        ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)), ((nb090AlphaDummy549 A),
        (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A),
        (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
                                unfold nb090AlphaDummy557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
                                unfold nb090AlphaDummy558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                            ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                            ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                            ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
                            ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
                            ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                            ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                            ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
                            ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
                              unfold nb090AlphaDummy557;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                          (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
                              unfold nb090AlphaDummy558;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
                                unfold nb090AlphaDummy557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
                                unfold nb090AlphaDummy558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                            ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                            ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                            ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
                            ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
                            ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                            ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                            ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
                            ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                            ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                            ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                            ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                            ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                            ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                            ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                            ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                            ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                            ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                            ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                            ((nb090AlphaDummy001 A), u),
                            ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy553 A) from (by
                        unfold nb090AlphaDummy553;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0560 A) 0))))
                    (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy555 h) from (by
                        unfold nb090AlphaDummy555;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0561 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy554 A) from (by
                          unfold nb090AlphaDummy554;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0560 A) 1))))
                      (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy556 h) from (by
                          unfold nb090AlphaDummy556;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0561 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy579 A) from (by
                            unfold nb090AlphaDummy579;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0590 A) 0))))
                        (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy580 h) from (by
                            unfold nb090AlphaDummy580;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0591 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy546 A) ≠ (nb090AlphaDummy577 A) from (by
                              unfold nb090AlphaDummy577;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0588 A) 0))))
                          (show (nb090AlphaDummy548 h) ≠ (nb090AlphaDummy578 h) from (by
                              unfold nb090AlphaDummy578;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0589 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy546 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy548 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy553 A) ≠
        (nb090AlphaDummy560 A) from (by
                                          unfold nb090AlphaDummy560;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0564 A) 1)))) (show
                                        (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy563 h)
                                        from (by
                                          unfold nb090AlphaDummy563;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0565 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy553 A) ≠
        (nb090AlphaDummy559 A) from (by
          unfold nb090AlphaDummy559;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0564 A) 0)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy562 h) from (by
          unfold nb090AlphaDummy562;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0565 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
          unfold nb090AlphaDummy557;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0562 A) 0)))) (show (nb090AlphaDummy555 h) ≠
        (nb090AlphaDummy558 h) from (by
          unfold nb090AlphaDummy558;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0563 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy561 A),
        (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A), (nb090AlphaDummy563 h)),
        ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)), ((nb090AlphaDummy557 A),
        (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
        ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)), ((nb090AlphaDummy579 A),
        (nb090AlphaDummy580 h)), ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
        ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)), ((nb090AlphaDummy545 A),
        (nb090AlphaDummy547 h)), ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
        ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0568
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0569
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0566
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0567
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy567 A) from (by
          unfold
            nb090AlphaDummy567;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0572
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy568 h) from (by
          unfold
            nb090AlphaDummy568;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0573
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy565 A) from (by
          unfold
            nb090AlphaDummy565;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0570
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy566 h) from (by
          unfold
            nb090AlphaDummy566;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0571
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy561 A), (nb090AlphaDummy564 h)), ((nb090AlphaDummy560 A),
        (nb090AlphaDummy563 h)), ((nb090AlphaDummy559 A), (nb090AlphaDummy562 h)),
        ((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)), ((nb090AlphaDummy553 A),
        (nb090AlphaDummy555 h)), ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
        ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)), ((nb090AlphaDummy577 A),
        (nb090AlphaDummy578 h)), ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
        ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)), ((nb090AlphaDummy575 A),
        (nb090AlphaDummy576 h)), ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A),
        (nb090AlphaDummy505 h)), ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy555 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠ (nb090AlphaDummy571 A) from (by
          unfold
            nb090AlphaDummy571;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0576
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy572 h) from (by
          unfold
            nb090AlphaDummy572;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0577
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy560 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0574
                    A)
                  0)))) (show (nb090AlphaDummy563 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0575
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy553
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy561 A) ≠ (nb090AlphaDummy573 A) from (by
          unfold
            nb090AlphaDummy573;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0580
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy574 h) from (by
          unfold
            nb090AlphaDummy574;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0581
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy561 A) ≠
        (nb090AlphaDummy569 A) from (by
          unfold
            nb090AlphaDummy569;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0578
                    A)
                  0)))) (show (nb090AlphaDummy564 h) ≠ (nb090AlphaDummy570 h) from (by
          unfold
            nb090AlphaDummy570;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0579
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                (by
                                  unfold nb090AlphaDummy557;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                              (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from
                                (by
                                  unfold nb090AlphaDummy558;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                              ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                              ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                              ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
                              ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
                              ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                              ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                              ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
                              ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from (by
                                unfold nb090AlphaDummy557;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                            (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from (by
                                unfold nb090AlphaDummy558;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy553 A) ≠ (nb090AlphaDummy557 A) from
                                (by
                                  unfold nb090AlphaDummy557;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0562 A) 0))))
                              (show (nb090AlphaDummy555 h) ≠ (nb090AlphaDummy558 h) from
                                (by
                                  unfold nb090AlphaDummy558;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0563 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy557 A), (nb090AlphaDummy558 h)),
                              ((nb090AlphaDummy553 A), (nb090AlphaDummy555 h)),
                              ((nb090AlphaDummy554 A), (nb090AlphaDummy556 h)),
                              ((nb090AlphaDummy579 A), (nb090AlphaDummy580 h)),
                              ((nb090AlphaDummy577 A), (nb090AlphaDummy578 h)),
                              ((nb090AlphaDummy546 A), (nb090AlphaDummy548 h)),
                              ((nb090AlphaDummy545 A), (nb090AlphaDummy547 h)),
                              ((nb090AlphaDummy575 A), (nb090AlphaDummy576 h)),
                              ((nb090AlphaDummy549 A), (nb090AlphaDummy550 h)),
                              ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                              ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                              ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                              ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                              ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                              ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                              ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                              ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                              ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                              ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
                              ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                (nb090AlphaDummy004 v u A h))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0046`. -/
@[expose]
noncomputable def nb090SplitAlpha0046 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
        ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
        ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
        ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
        ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
          (Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy141 A))
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
          (Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy142 h))
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                      unfold nb090AlphaDummy136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                      unfold nb090AlphaDummy138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                        unfold nb090AlphaDummy135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                        unfold nb090AlphaDummy137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                          unfold nb090AlphaDummy141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                          unfold nb090AlphaDummy142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                            unfold nb090AlphaDummy139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                            unfold nb090AlphaDummy140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                              unfold nb090AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                              unfold nb090AlphaDummy145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from (by
                                unfold nb090AlphaDummy144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from (by
                                unfold nb090AlphaDummy146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                    (by
                                      unfold nb090AlphaDummy147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from
                                    (by
                                      unfold nb090AlphaDummy148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                    ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                    ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                    ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                    ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                    ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                    ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                    ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                    ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                    ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                    ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                    ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                    ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                    ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                    ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                    ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                    ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                    ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                    ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                    ((nb090AlphaDummy000 A), h),
                                    ((nb090AlphaDummy002 A), v),
                                    ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
                                      (nb090AlphaDummy004 v u A h))]
                                  (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
                        unfold nb090AlphaDummy136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
                        unfold nb090AlphaDummy138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
                          unfold nb090AlphaDummy135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
                          unfold nb090AlphaDummy137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy141 A) from (by
                            unfold nb090AlphaDummy141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy142 h) from (by
                            unfold nb090AlphaDummy142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy139 A) from (by
                              unfold nb090AlphaDummy139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy140 h) from (by
                              unfold nb090AlphaDummy140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy129 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy131 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy143 A) from (by
                                unfold nb090AlphaDummy143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy145 h) from (by
                                unfold nb090AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy136 A) ≠ (nb090AlphaDummy144 A) from
                                (by
                                  unfold nb090AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090AlphaDummy138 h) ≠ (nb090AlphaDummy146 h) from
                                (by
                                  unfold nb090AlphaDummy146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy150 A) from (by
          unfold nb090AlphaDummy150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090AlphaDummy145 h) ≠
        (nb090AlphaDummy153 h) from (by
          unfold nb090AlphaDummy153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy149 A) from (by
          unfold nb090AlphaDummy149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy152 h) from (by
          unfold nb090AlphaDummy152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy143 A) ≠
        (nb090AlphaDummy147 A) from (by
          unfold nb090AlphaDummy147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h) from (by
          unfold nb090AlphaDummy148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠ (nb090AlphaDummy157 A) from (by
          unfold
            nb090AlphaDummy157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy158 h) from (by
          unfold
            nb090AlphaDummy158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy155 A) from (by
          unfold
            nb090AlphaDummy155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy156 h) from (by
          unfold
            nb090AlphaDummy156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy151 A), (nb090AlphaDummy154 h)), ((nb090AlphaDummy150 A),
        (nb090AlphaDummy153 h)), ((nb090AlphaDummy149 A), (nb090AlphaDummy152 h)),
        ((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)), ((nb090AlphaDummy143 A),
        (nb090AlphaDummy145 h)), ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
        ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)), ((nb090AlphaDummy135 A),
        (nb090AlphaDummy137 h)), ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
        ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)), ((nb090AlphaDummy130 A),
        (nb090AlphaDummy132 h)), ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
        ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy145
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy150
        A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠ (nb090AlphaDummy161 A) from (by
          unfold
            nb090AlphaDummy161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy162 h) from (by
          unfold
            nb090AlphaDummy162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy150 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090AlphaDummy153 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy143
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy151
        A) ≠ (nb090AlphaDummy163 A) from (by
          unfold
            nb090AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy164 h) from (by
          unfold
            nb090AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy151 A) ≠
        (nb090AlphaDummy159 A) from (by
          unfold
            nb090AlphaDummy159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090AlphaDummy154 h) ≠ (nb090AlphaDummy160 h) from (by
          unfold
            nb090AlphaDummy160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))]
                                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A) from
                                      (by
                                        unfold nb090AlphaDummy147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090AlphaDummy145 h) ≠
                                        (nb090AlphaDummy148 h) from (by
                                        unfold nb090AlphaDummy148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy143 A) ≠ (nb090AlphaDummy147 A)
                                        from (by
                                          unfold nb090AlphaDummy147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090AlphaDummy145 h) ≠ (nb090AlphaDummy148 h)
                                        from (by
                                          unfold nb090AlphaDummy148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy147 A), (nb090AlphaDummy148 h)),
                                      ((nb090AlphaDummy143 A), (nb090AlphaDummy145 h)),
                                      ((nb090AlphaDummy144 A), (nb090AlphaDummy146 h)),
                                      ((nb090AlphaDummy136 A), (nb090AlphaDummy138 h)),
                                      ((nb090AlphaDummy135 A), (nb090AlphaDummy137 h)),
                                      ((nb090AlphaDummy141 A), (nb090AlphaDummy142 h)),
                                      ((nb090AlphaDummy139 A), (nb090AlphaDummy140 h)),
                                      ((nb090AlphaDummy130 A), (nb090AlphaDummy132 h)),
                                      ((nb090AlphaDummy129 A), (nb090AlphaDummy131 h)),
                                      ((nb090AlphaDummy133 A), (nb090AlphaDummy134 h)),
                                      ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
                                      ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
                                      ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)),
                                      ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
                                      ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
                                      ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
                                      ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
                                      ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
                                      ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
                                      ((nb090AlphaDummy000 A), h),
                                      ((nb090AlphaDummy002 A), v),
                                      ((nb090AlphaDummy001 A), u),
                                      ((nb090AlphaDummy003 A),
                                        (nb090AlphaDummy004 v u A h))] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
