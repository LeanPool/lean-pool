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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0061`. -/
@[expose]
noncomputable def nb095SplitAlpha0061 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy477 D R S_cls E), (nb095AlphaDummy478 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy477 D R S_cls E))
          (Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy477 D R S_cls E))
            (Class.cab (nb095AlphaDummy471 D R S_cls E)
              (synWrex (nb095AlphaDummy472 D R S_cls E)
                (Class.cv (nb095AlphaDummy465 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy478 f))
          (Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy478 f))
            (Class.cab (nb095AlphaDummy473 f)
              (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                  (synCphi (Class.cv (nb095AlphaDummy474 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                      (nb095AlphaDummy472 D R S_cls E) from (by
                      unfold nb095AlphaDummy472;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
                  (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy474 f) from (by
                      unfold nb095AlphaDummy474;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0476 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                        (nb095AlphaDummy471 D R S_cls E) from (by
                        unfold nb095AlphaDummy471;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 0))))
                    (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy473 f) from (by
                        unfold nb095AlphaDummy473;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0476 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy465 D R S_cls E) ≠
                          (nb095AlphaDummy477 D R S_cls E) from (by
                          unfold nb095AlphaDummy477;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0478 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy478 f) from (by
                          unfold nb095AlphaDummy478;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0479 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                            (nb095AlphaDummy475 D R S_cls E) from (by
                            unfold nb095AlphaDummy475;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0475 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy476 f) from (by
                            unfold nb095AlphaDummy476;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0477 f) 0))))
                        (TAlphaVar.there (freshVar_injective (((synCcnv
                                (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                            (by decide))
                          (freshVar_injective (((synCcnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy467 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy468 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                              (nb095AlphaDummy479 D R S_cls E) from (by
                              unfold nb095AlphaDummy479;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy481 f) from (by
                              unfold nb095AlphaDummy481;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                                (nb095AlphaDummy480 D R S_cls E) from (by
                                unfold nb095AlphaDummy480;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0480 D R S_cls E) 1))))
                            (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy482 f) from (by
                                unfold nb095AlphaDummy482;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy474 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy486 D R S_cls E) from (by
          unfold nb095AlphaDummy486;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy489 f) from (by
          unfold nb095AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy485 D R S_cls E) from (by
          unfold nb095AlphaDummy485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy488 f) from (by
          unfold nb095AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy483 D R S_cls E) from (by
          unfold nb095AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
          unfold nb095AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy487 D R S_cls E), (nb095AlphaDummy490 f)),
        ((nb095AlphaDummy486 D R S_cls E), (nb095AlphaDummy489 f)),
        ((nb095AlphaDummy485 D R S_cls E), (nb095AlphaDummy488 f)),
        ((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
        ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
        ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy477 D R S_cls E), (nb095AlphaDummy478 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy486
        D R S_cls E) ≠ (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy487 D R S_cls E), (nb095AlphaDummy490 f)),
        ((nb095AlphaDummy486 D R S_cls E), (nb095AlphaDummy489 f)),
        ((nb095AlphaDummy485 D R S_cls E), (nb095AlphaDummy488 f)),
        ((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
        ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
        ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy477 D R S_cls E), (nb095AlphaDummy478 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487
        D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487
        D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy479 D R S_cls E) ≠
                                        (nb095AlphaDummy483 D R S_cls E) from (by
                                        unfold nb095AlphaDummy483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                      (by
                                        unfold nb095AlphaDummy484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy483 D R S_cls E),
                                      (nb095AlphaDummy484 f)),
                                    ((nb095AlphaDummy479 D R S_cls E),
                                      (nb095AlphaDummy481 f)),
                                    ((nb095AlphaDummy480 D R S_cls E),
                                      (nb095AlphaDummy482 f)),
                                    ((nb095AlphaDummy472 D R S_cls E),
                                      (nb095AlphaDummy474 f)),
                                    ((nb095AlphaDummy471 D R S_cls E),
                                      (nb095AlphaDummy473 f)),
                                    ((nb095AlphaDummy477 D R S_cls E),
                                      (nb095AlphaDummy478 f)),
                                    ((nb095AlphaDummy475 D R S_cls E),
                                      (nb095AlphaDummy476 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
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
                                    (nb095AlphaDummy479 D R S_cls E) ≠
                                      (nb095AlphaDummy483 D R S_cls E) from (by
                                      unfold nb095AlphaDummy483;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                    (by
                                      unfold nb095AlphaDummy484;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0483 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy479 D R S_cls E) ≠
                                        (nb095AlphaDummy483 D R S_cls E) from (by
                                        unfold nb095AlphaDummy483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                      (by
                                        unfold nb095AlphaDummy484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy483 D R S_cls E),
                                      (nb095AlphaDummy484 f)),
                                    ((nb095AlphaDummy479 D R S_cls E),
                                      (nb095AlphaDummy481 f)),
                                    ((nb095AlphaDummy480 D R S_cls E),
                                      (nb095AlphaDummy482 f)),
                                    ((nb095AlphaDummy472 D R S_cls E),
                                      (nb095AlphaDummy474 f)),
                                    ((nb095AlphaDummy471 D R S_cls E),
                                      (nb095AlphaDummy473 f)),
                                    ((nb095AlphaDummy477 D R S_cls E),
                                      (nb095AlphaDummy478 f)),
                                    ((nb095AlphaDummy475 D R S_cls E),
                                      (nb095AlphaDummy476 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                        (nb095AlphaDummy472 D R S_cls E) from (by
                        unfold nb095AlphaDummy472;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E) 1))))
                    (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy474 f) from (by
                        unfold nb095AlphaDummy474;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0476 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy465 D R S_cls E) ≠
                          (nb095AlphaDummy471 D R S_cls E) from (by
                          unfold nb095AlphaDummy471;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0474 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy473 f) from (by
                          unfold nb095AlphaDummy473;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0476 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                            (nb095AlphaDummy477 D R S_cls E) from (by
                            unfold nb095AlphaDummy477;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0478 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy478 f) from (by
                            unfold nb095AlphaDummy478;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0479 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy465 D R S_cls E) ≠
                              (nb095AlphaDummy475 D R S_cls E) from (by
                              unfold nb095AlphaDummy475;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0475 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy467 f) ≠ (nb095AlphaDummy476 f) from (by
                              unfold nb095AlphaDummy476;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0477 f) 0))))
                          (TAlphaVar.there (freshVar_injective (((synCcnv
                                  (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
                              (by decide)) (freshVar_injective (((synCcnv (Class.cv f))).fv)
                              (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy467 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy468 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy472 D R S_cls E) ≠
                                (nb095AlphaDummy479 D R S_cls E) from (by
                                unfold nb095AlphaDummy479;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0480 D R S_cls E) 0))))
                            (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy481 f) from (by
                                unfold nb095AlphaDummy481;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                                  (nb095AlphaDummy480 D R S_cls E) from (by
                                  unfold nb095AlphaDummy480;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0480 D R S_cls E) 1))))
                              (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy482 f) from
                                (by
                                  unfold nb095AlphaDummy482;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy474 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy486 D R S_cls E) from (by
          unfold nb095AlphaDummy486;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy489 f) from (by
          unfold nb095AlphaDummy489;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy485 D R S_cls E) from (by
          unfold nb095AlphaDummy485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy488 f) from (by
          unfold nb095AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy483 D R S_cls E) from (by
          unfold nb095AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
          unfold nb095AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy487 D R S_cls E), (nb095AlphaDummy490 f)),
        ((nb095AlphaDummy486 D R S_cls E), (nb095AlphaDummy489 f)),
        ((nb095AlphaDummy485 D R S_cls E), (nb095AlphaDummy488 f)),
        ((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
        ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
        ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy477 D R S_cls E), (nb095AlphaDummy478 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy486
        D R S_cls E) ≠ (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy487 D R S_cls E), (nb095AlphaDummy490 f)),
        ((nb095AlphaDummy486 D R S_cls E), (nb095AlphaDummy489 f)),
        ((nb095AlphaDummy485 D R S_cls E), (nb095AlphaDummy488 f)),
        ((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
        ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
        ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy477 D R S_cls E), (nb095AlphaDummy478 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487
        D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487
        D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy483 D R S_cls E) from (by
                                          unfold nb095AlphaDummy483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0482 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy481 f) ≠
        (nb095AlphaDummy484 f) from (by
                                          unfold nb095AlphaDummy484;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0483 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy483 D R S_cls E),
                                        (nb095AlphaDummy484 f)),
                                      ((nb095AlphaDummy479 D R S_cls E),
                                        (nb095AlphaDummy481 f)),
                                      ((nb095AlphaDummy480 D R S_cls E),
                                        (nb095AlphaDummy482 f)),
                                      ((nb095AlphaDummy472 D R S_cls E),
                                        (nb095AlphaDummy474 f)),
                                      ((nb095AlphaDummy471 D R S_cls E),
                                        (nb095AlphaDummy473 f)),
                                      ((nb095AlphaDummy477 D R S_cls E),
                                        (nb095AlphaDummy478 f)),
                                      ((nb095AlphaDummy475 D R S_cls E),
                                        (nb095AlphaDummy476 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
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
                                      (nb095AlphaDummy479 D R S_cls E) ≠
                                        (nb095AlphaDummy483 D R S_cls E) from (by
                                        unfold nb095AlphaDummy483;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0482 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                      (by
                                        unfold nb095AlphaDummy484;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0483 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy483 D R S_cls E) from (by
                                          unfold nb095AlphaDummy483;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0482 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy481 f) ≠
        (nb095AlphaDummy484 f) from (by
                                          unfold nb095AlphaDummy484;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0483 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy483 D R S_cls E),
                                        (nb095AlphaDummy484 f)),
                                      ((nb095AlphaDummy479 D R S_cls E),
                                        (nb095AlphaDummy481 f)),
                                      ((nb095AlphaDummy480 D R S_cls E),
                                        (nb095AlphaDummy482 f)),
                                      ((nb095AlphaDummy472 D R S_cls E),
                                        (nb095AlphaDummy474 f)),
                                      ((nb095AlphaDummy471 D R S_cls E),
                                        (nb095AlphaDummy473 f)),
                                      ((nb095AlphaDummy477 D R S_cls E),
                                        (nb095AlphaDummy478 f)),
                                      ((nb095AlphaDummy475 D R S_cls E),
                                        (nb095AlphaDummy476 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0062`. -/
@[expose]
noncomputable def nb095SplitAlpha0062 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
        ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy505 D R S_cls E))
          (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy505 D R S_cls E))
            (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy506 f))
          (synCphi (Class.cv (nb095AlphaDummy474 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy506 f))
            (synCphi (Class.cv (nb095AlphaDummy474 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                      (nb095AlphaDummy479 D R S_cls E) from (by
                      unfold nb095AlphaDummy479;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 0))))
                  (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy481 f) from (by
                      unfold nb095AlphaDummy481;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0481 f) 0))))
                  (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                        (nb095AlphaDummy480 D R S_cls E) from (by
                        unfold nb095AlphaDummy480;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 1))))
                    (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy482 f) from (by
                        unfold nb095AlphaDummy482;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0481 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy472 D R S_cls E) ≠
                          (nb095AlphaDummy505 D R S_cls E) from (by
                          unfold nb095AlphaDummy505;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0510 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy506 f) from (by
                          unfold nb095AlphaDummy506;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0511 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                            (nb095AlphaDummy503 D R S_cls E) from (by
                            unfold nb095AlphaDummy503;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0508 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy504 f) from (by
                            unfold nb095AlphaDummy504;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0509 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy474 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy479 D R S_cls E) ≠
                                        (nb095AlphaDummy486 D R S_cls E) from (by
                                        unfold nb095AlphaDummy486;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0484 D R S_cls E) 1)))) (show
                                      (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy489 f) from
                                      (by
                                        unfold nb095AlphaDummy489;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0485 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy485 D R S_cls E) from (by
                                          unfold nb095AlphaDummy485;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0484 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy481 f) ≠
        (nb095AlphaDummy488 f) from (by
                                          unfold nb095AlphaDummy488;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0485 f) 0))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy483 D R S_cls E) from (by
          unfold nb095AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
          unfold nb095AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed
                                      [((nb095AlphaDummy487 D R S_cls E),
        (nb095AlphaDummy490 f)), ((nb095AlphaDummy486 D R S_cls E),
        (nb095AlphaDummy489 f)), ((nb095AlphaDummy485 D R S_cls E),
        (nb095AlphaDummy488 f)), ((nb095AlphaDummy483 D R S_cls E),
        (nb095AlphaDummy484 f)), ((nb095AlphaDummy479 D R S_cls E),
        (nb095AlphaDummy481 f)), ((nb095AlphaDummy480 D R S_cls E),
        (nb095AlphaDummy482 f)), ((nb095AlphaDummy505 D R S_cls E),
        (nb095AlphaDummy506 f)), ((nb095AlphaDummy503 D R S_cls E),
        (nb095AlphaDummy504 f)), ((nb095AlphaDummy472 D R S_cls E),
        (nb095AlphaDummy474 f)), ((nb095AlphaDummy471 D R S_cls E),
        (nb095AlphaDummy473 f)), ((nb095AlphaDummy501 D R S_cls E),
        (nb095AlphaDummy502 f)), ((nb095AlphaDummy475 D R S_cls E),
        (nb095AlphaDummy476 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy001 D R S_cls E), u),
                                        ((nb095AlphaDummy002 D R S_cls E), x),
                                        ((nb095AlphaDummy000 D R S_cls E), f)]
                                      (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy487 D R S_cls E),
        (nb095AlphaDummy490 f)), ((nb095AlphaDummy486 D R S_cls E),
        (nb095AlphaDummy489 f)), ((nb095AlphaDummy485 D R S_cls E),
        (nb095AlphaDummy488 f)), ((nb095AlphaDummy483 D R S_cls E),
        (nb095AlphaDummy484 f)), ((nb095AlphaDummy479 D R S_cls E),
        (nb095AlphaDummy481 f)), ((nb095AlphaDummy480 D R S_cls E),
        (nb095AlphaDummy482 f)), ((nb095AlphaDummy505 D R S_cls E),
        (nb095AlphaDummy506 f)), ((nb095AlphaDummy503 D R S_cls E),
        (nb095AlphaDummy504 f)), ((nb095AlphaDummy472 D R S_cls E),
        (nb095AlphaDummy474 f)), ((nb095AlphaDummy471 D R S_cls E),
        (nb095AlphaDummy473 f)), ((nb095AlphaDummy501 D R S_cls E),
        (nb095AlphaDummy502 f)), ((nb095AlphaDummy475 D R S_cls E),
        (nb095AlphaDummy476 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy479 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497 D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy497 D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy479 D R S_cls E) ≠
                                (nb095AlphaDummy483 D R S_cls E) from (by
                                unfold nb095AlphaDummy483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
                                unfold nb095AlphaDummy484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
                            ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
                            ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
                            ((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
                            ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
                            ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
                            ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
                            ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
                            ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
                            ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                            ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                            ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy479 D R S_cls E) ≠
                              (nb095AlphaDummy483 D R S_cls E) from (by
                              unfold nb095AlphaDummy483;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0482 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
                              unfold nb095AlphaDummy484;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy479 D R S_cls E) ≠
                                (nb095AlphaDummy483 D R S_cls E) from (by
                                unfold nb095AlphaDummy483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
                                unfold nb095AlphaDummy484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
                            ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
                            ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
                            ((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
                            ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
                            ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
                            ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
                            ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
                            ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
                            ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                            ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                            ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                            ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                            ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                            ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                            ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                            ((nb095AlphaDummy001 D R S_cls E), u),
                            ((nb095AlphaDummy002 D R S_cls E), x),
                            ((nb095AlphaDummy000 D R S_cls E), f)]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                        (nb095AlphaDummy479 D R S_cls E) from (by
                        unfold nb095AlphaDummy479;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E) 0))))
                    (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy481 f) from (by
                        unfold nb095AlphaDummy481;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0481 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy472 D R S_cls E) ≠
                          (nb095AlphaDummy480 D R S_cls E) from (by
                          unfold nb095AlphaDummy480;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0480 D R S_cls E)
                                  1))))
                      (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy482 f) from (by
                          unfold nb095AlphaDummy482;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0481 f) 1))))
                      (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                            (nb095AlphaDummy505 D R S_cls E) from (by
                            unfold nb095AlphaDummy505;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0510 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy506 f) from (by
                            unfold nb095AlphaDummy506;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0511 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy472 D R S_cls E) ≠
                              (nb095AlphaDummy503 D R S_cls E) from (by
                              unfold nb095AlphaDummy503;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0508 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy474 f) ≠ (nb095AlphaDummy504 f) from (by
                              unfold nb095AlphaDummy504;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0509 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy472 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy474 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095AlphaDummy479 D R S_cls E) ≠
        (nb095AlphaDummy486 D R S_cls E) from (by
                                          unfold nb095AlphaDummy486;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0484 D R S_cls E)
                                                  1)))) (show (nb095AlphaDummy481 f) ≠
        (nb095AlphaDummy489 f) from (by
                                          unfold nb095AlphaDummy489;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0485 f) 1))))
                                      (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy485 D R S_cls E) from (by
          unfold nb095AlphaDummy485;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0484 D R S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy488 f) from (by
          unfold nb095AlphaDummy488;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0485 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy479 D R S_cls E) ≠ (nb095AlphaDummy483 D R S_cls E) from (by
          unfold nb095AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0482 D R S_cls E)
                  0)))) (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
          unfold nb095AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0483 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed
                                        [((nb095AlphaDummy487 D R S_cls E),
        (nb095AlphaDummy490 f)), ((nb095AlphaDummy486 D R S_cls E),
        (nb095AlphaDummy489 f)), ((nb095AlphaDummy485 D R S_cls E),
        (nb095AlphaDummy488 f)), ((nb095AlphaDummy483 D R S_cls E),
        (nb095AlphaDummy484 f)), ((nb095AlphaDummy479 D R S_cls E),
        (nb095AlphaDummy481 f)), ((nb095AlphaDummy480 D R S_cls E),
        (nb095AlphaDummy482 f)), ((nb095AlphaDummy505 D R S_cls E),
        (nb095AlphaDummy506 f)), ((nb095AlphaDummy503 D R S_cls E),
        (nb095AlphaDummy504 f)), ((nb095AlphaDummy472 D R S_cls E),
        (nb095AlphaDummy474 f)), ((nb095AlphaDummy471 D R S_cls E),
        (nb095AlphaDummy473 f)), ((nb095AlphaDummy501 D R S_cls E),
        (nb095AlphaDummy502 f)), ((nb095AlphaDummy475 D R S_cls E),
        (nb095AlphaDummy476 f)), ((nb095AlphaDummy466 D R S_cls E),
        (nb095AlphaDummy468 f)), ((nb095AlphaDummy465 D R S_cls E),
        (nb095AlphaDummy467 f)), ((nb095AlphaDummy469 D R S_cls E),
        (nb095AlphaDummy470 f)), ((nb095AlphaDummy387 D R S_cls E),
        (nb095AlphaDummy390 f)), ((nb095AlphaDummy386 D R S_cls E),
        (nb095AlphaDummy389 f)), ((nb095AlphaDummy385 D R S_cls E),
        (nb095AlphaDummy388 f)), ((nb095AlphaDummy391 D R S_cls E),
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
                                        (synC1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493 D R S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy493 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0488
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0489
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0486
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0487
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy493 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy493;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0492
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy494 f) from (by
          unfold
            nb095AlphaDummy494;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0493
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy491 D R S_cls E) from (by
          unfold
            nb095AlphaDummy491;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0490
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy492 f) from (by
          unfold
            nb095AlphaDummy492;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0491
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy487 D R S_cls E), (nb095AlphaDummy490 f)),
        ((nb095AlphaDummy486 D R S_cls E), (nb095AlphaDummy489 f)),
        ((nb095AlphaDummy485 D R S_cls E), (nb095AlphaDummy488 f)),
        ((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
        ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
        ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
        ((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
        ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
        ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
        ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
        ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
        ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095AlphaDummy479 D R S_cls E))).fv ∪
        ((synC1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479 D R S_cls
        E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497 D R S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠ (nb095AlphaDummy497 D R
        S_cls E) from (by
          unfold
            nb095AlphaDummy497;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0496
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy498 f) from (by
          unfold
            nb095AlphaDummy498;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0497
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy486 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0494
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy489 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0495
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy479
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy481 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy487 D R S_cls E) ≠ (nb095AlphaDummy499 D R S_cls E) from (by
          unfold
            nb095AlphaDummy499;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0500
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy500 f) from (by
          unfold
            nb095AlphaDummy500;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0501
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy487 D R S_cls E) ≠
        (nb095AlphaDummy495 D R S_cls E) from (by
          unfold
            nb095AlphaDummy495;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0498
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy490 f) ≠ (nb095AlphaDummy496 f) from (by
          unfold
            nb095AlphaDummy496;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0499
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy479 D R S_cls E) ≠
                                  (nb095AlphaDummy483 D R S_cls E) from (by
                                  unfold nb095AlphaDummy483;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0482 D R S_cls E) 0))))
                              (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                (by
                                  unfold nb095AlphaDummy484;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
                              ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
                              ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
                              ((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
                              ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
                              ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
                              ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
                              ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
                              ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
                              ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                              ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                              ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy479 D R S_cls E) ≠
                                (nb095AlphaDummy483 D R S_cls E) from (by
                                unfold nb095AlphaDummy483;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0482 D R S_cls E) 0))))
                            (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from (by
                                unfold nb095AlphaDummy484;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb095AlphaDummy479 D R S_cls E) ≠
                                  (nb095AlphaDummy483 D R S_cls E) from (by
                                  unfold nb095AlphaDummy483;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0482 D R S_cls E) 0))))
                              (show (nb095AlphaDummy481 f) ≠ (nb095AlphaDummy484 f) from
                                (by
                                  unfold nb095AlphaDummy484;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0483 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb095AlphaDummy483 D R S_cls E), (nb095AlphaDummy484 f)),
                              ((nb095AlphaDummy479 D R S_cls E), (nb095AlphaDummy481 f)),
                              ((nb095AlphaDummy480 D R S_cls E), (nb095AlphaDummy482 f)),
                              ((nb095AlphaDummy505 D R S_cls E), (nb095AlphaDummy506 f)),
                              ((nb095AlphaDummy503 D R S_cls E), (nb095AlphaDummy504 f)),
                              ((nb095AlphaDummy472 D R S_cls E), (nb095AlphaDummy474 f)),
                              ((nb095AlphaDummy471 D R S_cls E), (nb095AlphaDummy473 f)),
                              ((nb095AlphaDummy501 D R S_cls E), (nb095AlphaDummy502 f)),
                              ((nb095AlphaDummy475 D R S_cls E), (nb095AlphaDummy476 f)),
                              ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
                              ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
                              ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
                              ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
                              ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
                              ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
                              ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0063`. -/
@[expose]
noncomputable def nb095SplitAlpha0063 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy513 D R S_cls E))
          (Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy513 D R S_cls E))
            (Class.cab (nb095AlphaDummy507 D R S_cls E)
              (synWrex (nb095AlphaDummy508 D R S_cls E)
                (Class.cv (nb095AlphaDummy466 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095AlphaDummy514 f))
          (Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095AlphaDummy514 f))
            (Class.cab (nb095AlphaDummy509 f)
              (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
                (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                  (synCphi (Class.cv (nb095AlphaDummy510 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                      (nb095AlphaDummy508 D R S_cls E) from (by
                      unfold nb095AlphaDummy508;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                  (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
                      unfold nb095AlphaDummy510;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0514 f) 1))))
                  (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                        (nb095AlphaDummy507 D R S_cls E) from (by
                        unfold nb095AlphaDummy507;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 0))))
                    (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
                        unfold nb095AlphaDummy509;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 0)))) (TAlphaVar.there
                      (show (nb095AlphaDummy466 D R S_cls E) ≠
                          (nb095AlphaDummy513 D R S_cls E) from (by
                          unfold nb095AlphaDummy513;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy514 f) from (by
                          unfold nb095AlphaDummy514;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                            (nb095AlphaDummy511 D R S_cls E) from (by
                            unfold nb095AlphaDummy511;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy512 f) from (by
                            unfold nb095AlphaDummy512;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
                      ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                      ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                              (nb095AlphaDummy515 D R S_cls E) from (by
                              unfold nb095AlphaDummy515;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0518 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                              unfold nb095AlphaDummy517;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                          (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                                (nb095AlphaDummy516 D R S_cls E) from (by
                                unfold nb095AlphaDummy516;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 1))))
                            (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from (by
                                unfold nb095AlphaDummy518;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095AlphaDummy510 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy522 D R S_cls E) from (by
          unfold nb095AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R S_cls
                    E)
                  1)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy525 f) from (by
          unfold nb095AlphaDummy525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy521 D R S_cls E) from (by
          unfold nb095AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy524 f) from (by
          unfold nb095AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy522
        D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy519 D R S_cls E),
                                      (nb095AlphaDummy520 f)),
                                    ((nb095AlphaDummy515 D R S_cls E),
                                      (nb095AlphaDummy517 f)),
                                    ((nb095AlphaDummy516 D R S_cls E),
                                      (nb095AlphaDummy518 f)),
                                    ((nb095AlphaDummy508 D R S_cls E),
                                      (nb095AlphaDummy510 f)),
                                    ((nb095AlphaDummy507 D R S_cls E),
                                      (nb095AlphaDummy509 f)),
                                    ((nb095AlphaDummy513 D R S_cls E),
                                      (nb095AlphaDummy514 f)),
                                    ((nb095AlphaDummy511 D R S_cls E),
                                      (nb095AlphaDummy512 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
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
                                    (nb095AlphaDummy515 D R S_cls E) ≠
                                      (nb095AlphaDummy519 D R S_cls E) from (by
                                      unfold nb095AlphaDummy519;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                    (by
                                      unfold nb095AlphaDummy520;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0521 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.reflOfClosed
                                  [((nb095AlphaDummy519 D R S_cls E),
                                      (nb095AlphaDummy520 f)),
                                    ((nb095AlphaDummy515 D R S_cls E),
                                      (nb095AlphaDummy517 f)),
                                    ((nb095AlphaDummy516 D R S_cls E),
                                      (nb095AlphaDummy518 f)),
                                    ((nb095AlphaDummy508 D R S_cls E),
                                      (nb095AlphaDummy510 f)),
                                    ((nb095AlphaDummy507 D R S_cls E),
                                      (nb095AlphaDummy509 f)),
                                    ((nb095AlphaDummy513 D R S_cls E),
                                      (nb095AlphaDummy514 f)),
                                    ((nb095AlphaDummy511 D R S_cls E),
                                      (nb095AlphaDummy512 f)),
                                    ((nb095AlphaDummy466 D R S_cls E),
                                      (nb095AlphaDummy468 f)),
                                    ((nb095AlphaDummy465 D R S_cls E),
                                      (nb095AlphaDummy467 f)),
                                    ((nb095AlphaDummy469 D R S_cls E),
                                      (nb095AlphaDummy470 f)),
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
                  (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                        (nb095AlphaDummy508 D R S_cls E) from (by
                        unfold nb095AlphaDummy508;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E) 1))))
                    (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy510 f) from (by
                        unfold nb095AlphaDummy510;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0514 f) 1)))) (TAlphaVar.there
                      (show (nb095AlphaDummy466 D R S_cls E) ≠
                          (nb095AlphaDummy507 D R S_cls E) from (by
                          unfold nb095AlphaDummy507;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0512 D R S_cls E)
                                  0))))
                      (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy509 f) from (by
                          unfold nb095AlphaDummy509;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0514 f) 0))))
                      (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                            (nb095AlphaDummy513 D R S_cls E) from (by
                            unfold nb095AlphaDummy513;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0516 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy514 f) from (by
                            unfold nb095AlphaDummy514;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0517 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy466 D R S_cls E) ≠
                              (nb095AlphaDummy511 D R S_cls E) from (by
                              unfold nb095AlphaDummy511;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0513 D R S_cls E)
                                      0))))
                          (show (nb095AlphaDummy468 f) ≠ (nb095AlphaDummy512 f) from (by
                              unfold nb095AlphaDummy512;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0515 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095AlphaDummy466 D R S_cls E))).fv ∪
                        ((Class.cv (nb095AlphaDummy465 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095AlphaDummy468 f))).fv ∪
                        ((Class.cv (nb095AlphaDummy467 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095AlphaDummy508 D R S_cls E) ≠
                                (nb095AlphaDummy515 D R S_cls E) from (by
                                unfold nb095AlphaDummy515;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0518 D R S_cls E) 0))))
                            (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy517 f) from (by
                                unfold nb095AlphaDummy517;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0519 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy508 D R S_cls E) ≠
                                  (nb095AlphaDummy516 D R S_cls E) from (by
                                  unfold nb095AlphaDummy516;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0518 D R S_cls E) 1))))
                              (show (nb095AlphaDummy510 f) ≠ (nb095AlphaDummy518 f) from
                                (by
                                  unfold nb095AlphaDummy518;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0519 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095AlphaDummy508 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095AlphaDummy510 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy522 D R S_cls E) from (by
          unfold nb095AlphaDummy522;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  1)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy525 f) from (by
          unfold nb095AlphaDummy525;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy515 D R S_cls E) ≠ (nb095AlphaDummy521 D R S_cls E) from (by
          unfold nb095AlphaDummy521;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0522 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy524 f) from (by
          unfold nb095AlphaDummy524;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0523 f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
          unfold nb095AlphaDummy519;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0520 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from (by
          unfold nb095AlphaDummy520;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0521 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy522
        D R S_cls E) ≠ (nb095AlphaDummy529 D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0526
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0527
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0524
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0525
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠ (nb095AlphaDummy529
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy529;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0530
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy530 f) from (by
          unfold
            nb095AlphaDummy530;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0531
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy527 D R S_cls E) from (by
          unfold
            nb095AlphaDummy527;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0528
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy528 f) from (by
          unfold
            nb095AlphaDummy528;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0529
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy523 D R S_cls E), (nb095AlphaDummy526 f)),
        ((nb095AlphaDummy522 D R S_cls E), (nb095AlphaDummy525 f)),
        ((nb095AlphaDummy521 D R S_cls E), (nb095AlphaDummy524 f)),
        ((nb095AlphaDummy519 D R S_cls E), (nb095AlphaDummy520 f)),
        ((nb095AlphaDummy515 D R S_cls E), (nb095AlphaDummy517 f)),
        ((nb095AlphaDummy516 D R S_cls E), (nb095AlphaDummy518 f)),
        ((nb095AlphaDummy508 D R S_cls E), (nb095AlphaDummy510 f)),
        ((nb095AlphaDummy507 D R S_cls E), (nb095AlphaDummy509 f)),
        ((nb095AlphaDummy513 D R S_cls E), (nb095AlphaDummy514 f)),
        ((nb095AlphaDummy511 D R S_cls E), (nb095AlphaDummy512 f)),
        ((nb095AlphaDummy466 D R S_cls E), (nb095AlphaDummy468 f)),
        ((nb095AlphaDummy465 D R S_cls E), (nb095AlphaDummy467 f)),
        ((nb095AlphaDummy469 D R S_cls E), (nb095AlphaDummy470 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy515 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515 D R
        S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠ (nb095AlphaDummy533
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy533;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0534
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy534 f) from (by
          unfold
            nb095AlphaDummy534;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0535
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy522 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0532
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy525 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0533
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy515
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy517 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy523
        D R S_cls E) ≠ (nb095AlphaDummy535 D R S_cls E) from (by
          unfold
            nb095AlphaDummy535;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0538
                    D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy536 f) from (by
          unfold
            nb095AlphaDummy536;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0539
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy523 D R S_cls E) ≠
        (nb095AlphaDummy531 D R S_cls E) from (by
          unfold
            nb095AlphaDummy531;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0536
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095AlphaDummy526 f) ≠ (nb095AlphaDummy532 f) from (by
          unfold
            nb095AlphaDummy532;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0537
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
                                          unfold nb095AlphaDummy519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy520 f) from (by
                                          unfold nb095AlphaDummy520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy519 D R S_cls E),
                                        (nb095AlphaDummy520 f)),
                                      ((nb095AlphaDummy515 D R S_cls E),
                                        (nb095AlphaDummy517 f)),
                                      ((nb095AlphaDummy516 D R S_cls E),
                                        (nb095AlphaDummy518 f)),
                                      ((nb095AlphaDummy508 D R S_cls E),
                                        (nb095AlphaDummy510 f)),
                                      ((nb095AlphaDummy507 D R S_cls E),
                                        (nb095AlphaDummy509 f)),
                                      ((nb095AlphaDummy513 D R S_cls E),
                                        (nb095AlphaDummy514 f)),
                                      ((nb095AlphaDummy511 D R S_cls E),
                                        (nb095AlphaDummy512 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
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
                                      (nb095AlphaDummy515 D R S_cls E) ≠
                                        (nb095AlphaDummy519 D R S_cls E) from (by
                                        unfold nb095AlphaDummy519;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0520 D R S_cls E) 0)))) (show
                                      (nb095AlphaDummy517 f) ≠ (nb095AlphaDummy520 f) from
                                      (by
                                        unfold nb095AlphaDummy520;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0521 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095AlphaDummy515 D R S_cls E) ≠
        (nb095AlphaDummy519 D R S_cls E) from (by
                                          unfold nb095AlphaDummy519;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0520 D R S_cls E)
                                                  0)))) (show (nb095AlphaDummy517 f) ≠
        (nb095AlphaDummy520 f) from (by
                                          unfold nb095AlphaDummy520;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0521 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                                    [((nb095AlphaDummy519 D R S_cls E),
                                        (nb095AlphaDummy520 f)),
                                      ((nb095AlphaDummy515 D R S_cls E),
                                        (nb095AlphaDummy517 f)),
                                      ((nb095AlphaDummy516 D R S_cls E),
                                        (nb095AlphaDummy518 f)),
                                      ((nb095AlphaDummy508 D R S_cls E),
                                        (nb095AlphaDummy510 f)),
                                      ((nb095AlphaDummy507 D R S_cls E),
                                        (nb095AlphaDummy509 f)),
                                      ((nb095AlphaDummy513 D R S_cls E),
                                        (nb095AlphaDummy514 f)),
                                      ((nb095AlphaDummy511 D R S_cls E),
                                        (nb095AlphaDummy512 f)),
                                      ((nb095AlphaDummy466 D R S_cls E),
                                        (nb095AlphaDummy468 f)),
                                      ((nb095AlphaDummy465 D R S_cls E),
                                        (nb095AlphaDummy467 f)),
                                      ((nb095AlphaDummy469 D R S_cls E),
                                        (nb095AlphaDummy470 f)),
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
