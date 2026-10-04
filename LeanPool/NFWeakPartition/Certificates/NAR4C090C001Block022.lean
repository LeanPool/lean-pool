/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block021

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part063`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0041`. -/
@[expose]
noncomputable def nb090SplitAlpha0041 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
        ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
        ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
        ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy501 A))
          (synCphi (Class.cv (nb090AlphaDummy468 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy501 A))
            (synCphi (Class.cv (nb090AlphaDummy468 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy502 h))
          (synCphi (Class.cv (nb090AlphaDummy470 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy502 h))
            (synCphi (Class.cv (nb090AlphaDummy470 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy475 A) from (by
                      unfold nb090AlphaDummy475;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                  (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy477 h) from (by
                      unfold nb090AlphaDummy477;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0481 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy476 A) from (by
                        unfold nb090AlphaDummy476;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                    (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy478 h) from (by
                        unfold nb090AlphaDummy478;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0481 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy501 A) from (by
                          unfold nb090AlphaDummy501;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0510 A) 0))))
                      (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy502 h) from (by
                          unfold nb090AlphaDummy502;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0511 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy499 A) from (by
                            unfold nb090AlphaDummy499;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0508 A) 0))))
                        (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy500 h) from (by
                            unfold nb090AlphaDummy500;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0509 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy468 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy470 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy482 A) from
                                      (by
                                        unfold nb090AlphaDummy482;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0484 A)
                                                1)))) (show (nb090AlphaDummy477 h) ≠
                                        (nb090AlphaDummy485 h) from (by
                                        unfold nb090AlphaDummy485;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0485 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy481 A)
                                        from (by
                                          unfold nb090AlphaDummy481;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0484 A) 0)))) (show
                                        (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy484 h)
                                        from (by
                                          unfold nb090AlphaDummy484;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0485 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy475 A) ≠
        (nb090AlphaDummy479 A) from (by
          unfold nb090AlphaDummy479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A) 0)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy480 h) from (by
          unfold nb090AlphaDummy480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy483 A),
        (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A), (nb090AlphaDummy485 h)),
                                        ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
                                        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                                        ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                                        ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                                        ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
                                        ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
                                        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                                        ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                                        ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
                                        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
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
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)),
        ((nb090AlphaDummy482 A), (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A),
        (nb090AlphaDummy484 h)), ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
        ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A),
        (nb090AlphaDummy478 h)), ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
        ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)), ((nb090AlphaDummy468 A),
        (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
        ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)), ((nb090AlphaDummy471 A),
        (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)),
        ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A),
        (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)),
        ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A),
        (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
                                unfold nb090AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                            (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
                                unfold nb090AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                            ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                            ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                            ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
                            ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
                            ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                            ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                            ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
                            ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
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
                          (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
                              unfold nb090AlphaDummy479;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                          (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
                              unfold nb090AlphaDummy480;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
                                unfold nb090AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                            (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
                                unfold nb090AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                            ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                            ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                            ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
                            ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
                            ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                            ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                            ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
                            ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
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
                    (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy475 A) from (by
                        unfold nb090AlphaDummy475;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0480 A) 0))))
                    (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy477 h) from (by
                        unfold nb090AlphaDummy477;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0481 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy476 A) from (by
                          unfold nb090AlphaDummy476;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0480 A) 1))))
                      (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy478 h) from (by
                          unfold nb090AlphaDummy478;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0481 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy501 A) from (by
                            unfold nb090AlphaDummy501;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0510 A) 0))))
                        (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy502 h) from (by
                            unfold nb090AlphaDummy502;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0511 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy468 A) ≠ (nb090AlphaDummy499 A) from (by
                              unfold nb090AlphaDummy499;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0508 A) 0))))
                          (show (nb090AlphaDummy470 h) ≠ (nb090AlphaDummy500 h) from (by
                              unfold nb090AlphaDummy500;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0509 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy468 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy470 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy475 A) ≠
        (nb090AlphaDummy482 A) from (by
                                          unfold nb090AlphaDummy482;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0484 A) 1)))) (show
                                        (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy485 h)
                                        from (by
                                          unfold nb090AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0485 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy475 A) ≠
        (nb090AlphaDummy481 A) from (by
          unfold nb090AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0484 A) 0)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy484 h) from (by
          unfold nb090AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0485 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
          unfold nb090AlphaDummy479;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0482 A) 0)))) (show (nb090AlphaDummy477 h) ≠
        (nb090AlphaDummy480 h) from (by
          unfold nb090AlphaDummy480;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0483 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy483 A),
        (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A), (nb090AlphaDummy485 h)),
        ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)), ((nb090AlphaDummy479 A),
        (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
        ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)), ((nb090AlphaDummy501 A),
        (nb090AlphaDummy502 h)), ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
        ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)), ((nb090AlphaDummy467 A),
        (nb090AlphaDummy469 h)), ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
        ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)), ((nb090AlphaDummy425 A),
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
        (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0488
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0489
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0486
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0487
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy489 A) from (by
          unfold
            nb090AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0492
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy490 h) from (by
          unfold
            nb090AlphaDummy490;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0493
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy487 A) from (by
          unfold
            nb090AlphaDummy487;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0490
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy488 h) from (by
          unfold
            nb090AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0491
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy483 A), (nb090AlphaDummy486 h)), ((nb090AlphaDummy482 A),
        (nb090AlphaDummy485 h)), ((nb090AlphaDummy481 A), (nb090AlphaDummy484 h)),
        ((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)), ((nb090AlphaDummy475 A),
        (nb090AlphaDummy477 h)), ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
        ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)), ((nb090AlphaDummy499 A),
        (nb090AlphaDummy500 h)), ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
        ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)), ((nb090AlphaDummy497 A),
        (nb090AlphaDummy498 h)), ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
        ((nb090AlphaDummy425 A), (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A),
        (nb090AlphaDummy427 h)), ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)),
        ((nb090AlphaDummy429 A), (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A),
        (nb090AlphaDummy422 h)), ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)),
        ((nb090AlphaDummy000 A), h), ((nb090AlphaDummy002 A), v),
        ((nb090AlphaDummy001 A), u), ((nb090AlphaDummy003 A),
        (nb090AlphaDummy004 v u A h))] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy477 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠ (nb090AlphaDummy493 A) from (by
          unfold
            nb090AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0496
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy494 h) from (by
          unfold
            nb090AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0497
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy482 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0494
                    A)
                  0)))) (show (nb090AlphaDummy485 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0495
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy475
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy483 A) ≠ (nb090AlphaDummy495 A) from (by
          unfold
            nb090AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0500
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy496 h) from (by
          unfold
            nb090AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0501
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy483 A) ≠
        (nb090AlphaDummy491 A) from (by
          unfold
            nb090AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0498
                    A)
                  0)))) (show (nb090AlphaDummy486 h) ≠ (nb090AlphaDummy492 h) from (by
          unfold
            nb090AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0499
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                (by
                                  unfold nb090AlphaDummy479;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                              (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from
                                (by
                                  unfold nb090AlphaDummy480;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                              ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                              ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                              ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
                              ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
                              ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                              ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                              ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
                              ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
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
                            (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from (by
                                unfold nb090AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                            (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from (by
                                unfold nb090AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy475 A) ≠ (nb090AlphaDummy479 A) from
                                (by
                                  unfold nb090AlphaDummy479;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0482 A) 0))))
                              (show (nb090AlphaDummy477 h) ≠ (nb090AlphaDummy480 h) from
                                (by
                                  unfold nb090AlphaDummy480;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0483 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy479 A), (nb090AlphaDummy480 h)),
                              ((nb090AlphaDummy475 A), (nb090AlphaDummy477 h)),
                              ((nb090AlphaDummy476 A), (nb090AlphaDummy478 h)),
                              ((nb090AlphaDummy501 A), (nb090AlphaDummy502 h)),
                              ((nb090AlphaDummy499 A), (nb090AlphaDummy500 h)),
                              ((nb090AlphaDummy468 A), (nb090AlphaDummy470 h)),
                              ((nb090AlphaDummy467 A), (nb090AlphaDummy469 h)),
                              ((nb090AlphaDummy497 A), (nb090AlphaDummy498 h)),
                              ((nb090AlphaDummy471 A), (nb090AlphaDummy472 h)),
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

/-! Certificates from `NAR4C090C001Part064`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0042`. -/
@[expose]
noncomputable def nb090SplitAlpha0042 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy515 A))
          (Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy515 A))
            (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCphi (Class.cv (nb090AlphaDummy510 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy516 h))
          (Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy516 h))
            (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCphi (Class.cv (nb090AlphaDummy512 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy510 A) from (by
                      unfold nb090AlphaDummy510;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
                  (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy512 h) from (by
                      unfold nb090AlphaDummy512;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy509 A) from (by
                        unfold nb090AlphaDummy509;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
                    (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy511 h) from (by
                        unfold nb090AlphaDummy511;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0518 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy515 A) from (by
                          unfold nb090AlphaDummy515;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0520 A) 0))))
                      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy516 h) from (by
                          unfold nb090AlphaDummy516;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0521 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy513 A) from (by
                            unfold nb090AlphaDummy513;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0517 A) 0))))
                        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy514 h) from (by
                            unfold nb090AlphaDummy514;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0519 h) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) (by decide))
                          (freshVar_injective (((synCcnv (Class.cv h))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090AlphaDummy503 A))).fv ∪
                      ((Class.cv (nb090AlphaDummy504 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090AlphaDummy505 h))).fv ∪
                      ((Class.cv (nb090AlphaDummy506 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy517 A) from (by
                              unfold nb090AlphaDummy517;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                          (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy519 h) from (by
                              unfold nb090AlphaDummy519;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                          (TAlphaVar.there
                            (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy518 A) from (by
                                unfold nb090AlphaDummy518;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                            (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy520 h) from (by
                                unfold nb090AlphaDummy520;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090AlphaDummy510 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090AlphaDummy512 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy524 A) from (by
          unfold nb090AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 1)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy527 h) from (by
          unfold nb090AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy523 A) from (by
          unfold nb090AlphaDummy523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 0)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy526 h) from (by
          unfold nb090AlphaDummy526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
          unfold nb090AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A)
                  0)))) (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
          unfold nb090AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A),
        (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A),
        (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A),
        (nb090AlphaDummy511 h)), ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A),
        (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A),
        (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A),
        (nb090AlphaDummy511 h)), ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy524
        A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525
        A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525
        A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                      (by
                                        unfold nb090AlphaDummy521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090AlphaDummy519 h) ≠
                                        (nb090AlphaDummy522 h) from (by
                                        unfold nb090AlphaDummy522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                                    ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                                    ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                                    ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                                    ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                                    ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
                                    ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                                    (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                    (by
                                      unfold nb090AlphaDummy521;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0524 A)
                                              0)))) (show
                                    (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from
                                    (by
                                      unfold nb090AlphaDummy522;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0525 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                      (by
                                        unfold nb090AlphaDummy521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090AlphaDummy519 h) ≠
                                        (nb090AlphaDummy522 h) from (by
                                        unfold nb090AlphaDummy522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                                    ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                                    ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                                    ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                                    ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                                    ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
                                    ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                    (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy510 A) from (by
                        unfold nb090AlphaDummy510;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
                    (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy512 h) from (by
                        unfold nb090AlphaDummy512;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0518 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy509 A) from (by
                          unfold nb090AlphaDummy509;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
                      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy511 h) from (by
                          unfold nb090AlphaDummy511;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy515 A) from (by
                            unfold nb090AlphaDummy515;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0520 A) 0))))
                        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy516 h) from (by
                            unfold nb090AlphaDummy516;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0521 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy513 A) from (by
                              unfold nb090AlphaDummy513;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0517 A) 0))))
                          (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy514 h) from (by
                              unfold nb090AlphaDummy514;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0519 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv h))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090AlphaDummy503 A))).fv ∪
                        ((Class.cv (nb090AlphaDummy504 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy505 h))).fv ∪
                        ((Class.cv (nb090AlphaDummy506 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy517 A) from (by
                                unfold nb090AlphaDummy517;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                            (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy519 h) from (by
                                unfold nb090AlphaDummy519;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                            (TAlphaVar.there
                              (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy518 A) from
                                (by
                                  unfold nb090AlphaDummy518;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                              (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy520 h) from
                                (by
                                  unfold nb090AlphaDummy520;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090AlphaDummy510 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090AlphaDummy512 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy524 A) from (by
          unfold nb090AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 1)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy527 h) from (by
          unfold nb090AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 1)))) (TAlphaVar.there (show
        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy523 A) from (by
          unfold nb090AlphaDummy523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A)
                  0)))) (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy526 h) from (by
          unfold nb090AlphaDummy526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy517 A) ≠
        (nb090AlphaDummy521 A) from (by
          unfold nb090AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A)
                  0)))) (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
          unfold nb090AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A),
        (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A),
        (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A),
        (nb090AlphaDummy511 h)), ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A),
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
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A),
        (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A),
        (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A),
        (nb090AlphaDummy511 h)), ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A),
        (nb090AlphaDummy506 h)), ((nb090AlphaDummy503 A), (nb090AlphaDummy505 h)),
        ((nb090AlphaDummy507 A), (nb090AlphaDummy508 h)), ((nb090AlphaDummy425 A),
        (nb090AlphaDummy428 h)), ((nb090AlphaDummy424 A), (nb090AlphaDummy427 h)),
        ((nb090AlphaDummy423 A), (nb090AlphaDummy426 h)), ((nb090AlphaDummy429 A),
        (nb090AlphaDummy430 h)), ((nb090AlphaDummy421 A), (nb090AlphaDummy422 h)),
        ((nb090AlphaDummy419 A), (nb090AlphaDummy420 h)), ((nb090AlphaDummy000 A), h),
        ((nb090AlphaDummy002 A), v), ((nb090AlphaDummy001 A), u),
        ((nb090AlphaDummy003 A), (nb090AlphaDummy004 v u A h))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy519
        h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy524
        A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525
        A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525
        A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A)
                                        from (by
                                          unfold nb090AlphaDummy521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0524 A) 0)))) (show
                                        (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h)
                                        from (by
                                          unfold nb090AlphaDummy522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0525 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                                      ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                                      ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                                      ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                                      ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                                      ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
                                      ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                                      (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                      (by
                                        unfold nb090AlphaDummy521;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0524 A)
                                                0)))) (show (nb090AlphaDummy519 h) ≠
                                        (nb090AlphaDummy522 h) from (by
                                        unfold nb090AlphaDummy522;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0525 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A)
                                        from (by
                                          unfold nb090AlphaDummy521;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0524 A) 0)))) (show
                                        (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h)
                                        from (by
                                          unfold nb090AlphaDummy522;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0525 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                                      ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                                      ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                                      ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                                      ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                                      ((nb090AlphaDummy515 A), (nb090AlphaDummy516 h)),
                                      ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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

/-! Certificates from `NAR4C090C001Part065`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb090_split_alpha_0043`. -/
@[expose]
noncomputable def nb090SplitAlpha0043 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
        ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
        ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
        ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy543 A))
          (synCphi (Class.cv (nb090AlphaDummy510 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy543 A))
            (synCphi (Class.cv (nb090AlphaDummy510 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090AlphaDummy544 h))
          (synCphi (Class.cv (nb090AlphaDummy512 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090AlphaDummy544 h))
            (synCphi (Class.cv (nb090AlphaDummy512 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy517 A) from (by
                      unfold nb090AlphaDummy517;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                  (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy519 h) from (by
                      unfold nb090AlphaDummy519;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0523 h) 0))))
                  (TAlphaVar.there
                    (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy518 A) from (by
                        unfold nb090AlphaDummy518;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                    (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy520 h) from (by
                        unfold nb090AlphaDummy520;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0523 h) 1)))) (TAlphaVar.there
                      (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy543 A) from (by
                          unfold nb090AlphaDummy543;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0552 A) 0))))
                      (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy544 h) from (by
                          unfold nb090AlphaDummy544;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0553 h) 0))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy541 A) from (by
                            unfold nb090AlphaDummy541;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0550 A) 0))))
                        (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy542 h) from (by
                            unfold nb090AlphaDummy542;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0551 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy510 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy512 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy524 A) from
                                      (by
                                        unfold nb090AlphaDummy524;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0526 A)
                                                1)))) (show (nb090AlphaDummy519 h) ≠
                                        (nb090AlphaDummy527 h) from (by
                                        unfold nb090AlphaDummy527;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0527 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy523 A)
                                        from (by
                                          unfold nb090AlphaDummy523;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0526 A) 0)))) (show
                                        (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy526 h)
                                        from (by
                                          unfold nb090AlphaDummy526;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0527 h) 0))))
                                      (TAlphaVar.there (show (nb090AlphaDummy517 A) ≠
        (nb090AlphaDummy521 A) from (by
          unfold nb090AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A) 0)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy522 h) from (by
          unfold nb090AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb090AlphaDummy525 A),
        (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A), (nb090AlphaDummy527 h)),
                                        ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
                                        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                                        ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                                        ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                                        ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
                                        ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
                                        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                                        ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                                        ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
                                        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)),
        ((nb090AlphaDummy524 A), (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A),
        (nb090AlphaDummy526 h)), ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
        ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A),
        (nb090AlphaDummy520 h)), ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
        ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)), ((nb090AlphaDummy510 A),
        (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
        ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)), ((nb090AlphaDummy513 A),
        (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A), (nb090AlphaDummy506 h)),
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
        (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
                                unfold nb090AlphaDummy521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
                                unfold nb090AlphaDummy522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                            ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                            ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                            ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
                            ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
                            ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                            ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                            ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
                            ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                          (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
                              unfold nb090AlphaDummy521;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                          (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
                              unfold nb090AlphaDummy522;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
                                unfold nb090AlphaDummy521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
                                unfold nb090AlphaDummy522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                            ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                            ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                            ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
                            ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
                            ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                            ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                            ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
                            ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                    (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy517 A) from (by
                        unfold nb090AlphaDummy517;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0522 A) 0))))
                    (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy519 h) from (by
                        unfold nb090AlphaDummy519;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0523 h) 0)))) (TAlphaVar.there
                      (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy518 A) from (by
                          unfold nb090AlphaDummy518;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0522 A) 1))))
                      (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy520 h) from (by
                          unfold nb090AlphaDummy520;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0523 h) 1))))
                      (TAlphaVar.there
                        (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy543 A) from (by
                            unfold nb090AlphaDummy543;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0552 A) 0))))
                        (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy544 h) from (by
                            unfold nb090AlphaDummy544;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0553 h) 0))))
                        (TAlphaVar.there
                          (show (nb090AlphaDummy510 A) ≠ (nb090AlphaDummy541 A) from (by
                              unfold nb090AlphaDummy541;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0550 A) 0))))
                          (show (nb090AlphaDummy512 h) ≠ (nb090AlphaDummy542 h) from (by
                              unfold nb090AlphaDummy542;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0551 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090AlphaDummy510 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090AlphaDummy512 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090AlphaDummy517 A) ≠
        (nb090AlphaDummy524 A) from (by
                                          unfold nb090AlphaDummy524;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0526 A) 1)))) (show
                                        (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy527 h)
                                        from (by
                                          unfold nb090AlphaDummy527;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0527 h) 1))))
                                      (TAlphaVar.there (show (nb090AlphaDummy517 A) ≠
        (nb090AlphaDummy523 A) from (by
          unfold nb090AlphaDummy523;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0526 A) 0)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy526 h) from (by
          unfold nb090AlphaDummy526;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0527 h) 0)))) (TAlphaVar.there (show
        (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
          unfold nb090AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0524 A) 0)))) (show (nb090AlphaDummy519 h) ≠
        (nb090AlphaDummy522 h) from (by
          unfold nb090AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0525 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb090AlphaDummy525 A),
        (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A), (nb090AlphaDummy527 h)),
        ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)), ((nb090AlphaDummy521 A),
        (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
        ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)), ((nb090AlphaDummy543 A),
        (nb090AlphaDummy544 h)), ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
        ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)), ((nb090AlphaDummy509 A),
        (nb090AlphaDummy511 h)), ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
        ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)), ((nb090AlphaDummy504 A),
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
        (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0530
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0531
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0528
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0529
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy531 A) from (by
          unfold
            nb090AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0534
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy532 h) from (by
          unfold
            nb090AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0535
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy529 A) from (by
          unfold
            nb090AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0532
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy530 h) from (by
          unfold
            nb090AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0533
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb090AlphaDummy525 A), (nb090AlphaDummy528 h)), ((nb090AlphaDummy524 A),
        (nb090AlphaDummy527 h)), ((nb090AlphaDummy523 A), (nb090AlphaDummy526 h)),
        ((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)), ((nb090AlphaDummy517 A),
        (nb090AlphaDummy519 h)), ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
        ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)), ((nb090AlphaDummy541 A),
        (nb090AlphaDummy542 h)), ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
        ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)), ((nb090AlphaDummy539 A),
        (nb090AlphaDummy540 h)), ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
        (freshVar_injective (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090AlphaDummy519 h))).fv ∪
        ((synC1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠ (nb090AlphaDummy535 A) from (by
          unfold
            nb090AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0538
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy536 h) from (by
          unfold
            nb090AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0539
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy524 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0536
                    A)
                  0)))) (show (nb090AlphaDummy527 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0537
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090AlphaDummy517
        A))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090AlphaDummy525 A) ≠ (nb090AlphaDummy537 A) from (by
          unfold
            nb090AlphaDummy537;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0542
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy538 h) from (by
          unfold
            nb090AlphaDummy538;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0543
                    h)
                  0)))) (TAlphaVar.there (show (nb090AlphaDummy525 A) ≠
        (nb090AlphaDummy533 A) from (by
          unfold
            nb090AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0540
                    A)
                  0)))) (show (nb090AlphaDummy528 h) ≠ (nb090AlphaDummy534 h) from (by
          unfold
            nb090AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0541
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                (by
                                  unfold nb090AlphaDummy521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                              (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from
                                (by
                                  unfold nb090AlphaDummy522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                              ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                              ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                              ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
                              ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
                              ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                              ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                              ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
                              ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
                            (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from (by
                                unfold nb090AlphaDummy521;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                            (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from (by
                                unfold nb090AlphaDummy522;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090AlphaDummy517 A) ≠ (nb090AlphaDummy521 A) from
                                (by
                                  unfold nb090AlphaDummy521;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0524 A) 0))))
                              (show (nb090AlphaDummy519 h) ≠ (nb090AlphaDummy522 h) from
                                (by
                                  unfold nb090AlphaDummy522;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0525 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb090AlphaDummy521 A), (nb090AlphaDummy522 h)),
                              ((nb090AlphaDummy517 A), (nb090AlphaDummy519 h)),
                              ((nb090AlphaDummy518 A), (nb090AlphaDummy520 h)),
                              ((nb090AlphaDummy543 A), (nb090AlphaDummy544 h)),
                              ((nb090AlphaDummy541 A), (nb090AlphaDummy542 h)),
                              ((nb090AlphaDummy510 A), (nb090AlphaDummy512 h)),
                              ((nb090AlphaDummy509 A), (nb090AlphaDummy511 h)),
                              ((nb090AlphaDummy539 A), (nb090AlphaDummy540 h)),
                              ((nb090AlphaDummy513 A), (nb090AlphaDummy514 h)),
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
