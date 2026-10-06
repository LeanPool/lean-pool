/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part055`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0158`. -/
@[expose]
noncomputable def nb068SplitAlpha0158 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy457))
          (Class.cv (nb068AlphaDummy450))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy458))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))
              (Class.cv (nb068AlphaDummy457))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy459 f))
          (Class.cv (nb068AlphaDummy452 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy460 f))
            (synCif (Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))
              (synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))
              (Class.cv (nb068AlphaDummy459 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy457) from (by
              unfold nb068AlphaDummy457;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0468) 0))))
          (show (nb068AlphaDummy452 f) ≠ (nb068AlphaDummy459 f) from (by
              unfold nb068AlphaDummy459;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0469 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy458) from (by
                unfold nb068AlphaDummy458;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0468) 1))))
            (show (nb068AlphaDummy452 f) ≠ (nb068AlphaDummy460 f) from (by
                unfold nb068AlphaDummy460;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0469 f) 1))))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy450))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb068AlphaDummy452 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy464) from (by
                                  unfold nb068AlphaDummy464;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0472) 1))))
                              (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy467 f) from
                                (by
                                  unfold nb068AlphaDummy467;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0473 f) 1))))
                              (TAlphaVar.there
                                (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy463) from (by
                                    unfold nb068AlphaDummy463;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0472) 0)))) (show
                                  (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy466 f) from (by
                                    unfold nb068AlphaDummy466;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0473 f)
                                            0)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from
                                    (by
                                      unfold nb068AlphaDummy461;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0470)
                                              0)))) (show
                                    (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from
                                    (by
                                      unfold nb068AlphaDummy462;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0471 f)
                                              0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
                                  ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
                                  ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
                                  ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                                  ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                                  ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                                  ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                                  ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                                  ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                                  ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                                  ((nb068AlphaDummy001), x), ((nb068AlphaDummy003),
                                    (nb068AlphaDummy004 x y f))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb068SplitAlpha0157 x y f))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                          unfold nb068AlphaDummy461;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                      (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                          unfold nb068AlphaDummy462;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                      ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                      ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                      ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                      ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                      ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                      ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                      ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                      ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                      ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from
                      (by
                        unfold nb068AlphaDummy461;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                    (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                        unfold nb068AlphaDummy462;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                          unfold nb068AlphaDummy461;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                      (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                          unfold nb068AlphaDummy462;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                      ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                      ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                      ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                      ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                      ((nb068AlphaDummy455), (nb068AlphaDummy456 f)),
                      ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                      ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                      ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                      ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                      ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                      ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                      ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                      ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                      ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                      ((nb068AlphaDummy001), x),
                      ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0159`. -/
@[expose]
noncomputable def nb068SplitAlpha0159 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
        ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
        ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
        ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
        ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
        ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy463))
            (synCun (Class.cv (nb068AlphaDummy464)) (Class.cv (nb068AlphaDummy465))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy467 f))
            (Class.cv (nb068AlphaDummy468 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy466 f))
            (synCun (Class.cv (nb068AlphaDummy467 f))
              (Class.cv (nb068AlphaDummy468 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0476) 0))))
                          (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0477 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0474) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0475 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy471) from (by
                              unfold nb068AlphaDummy471;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0480) 0))))
                          (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy472 f) from (by
                              unfold nb068AlphaDummy472;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0481 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy469) from (by
                                unfold nb068AlphaDummy469;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0478) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy470 f) from (by
                                unfold nb068AlphaDummy470;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0479 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
          ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
          ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
          ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
          ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
          ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
          ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
          ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
          ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
          ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
          ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
          ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy475) from (by
                                unfold nb068AlphaDummy475;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0484) 0))))
                            (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy476 f) from (by
                                unfold nb068AlphaDummy476;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0485 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy464) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0482) 0))))
                              (show (nb068AlphaDummy467 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0483 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy457))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy459 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy477) from (by
                                unfold nb068AlphaDummy477;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0488) 0))))
                            (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy478 f) from (by
                                unfold nb068AlphaDummy478;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0489 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy465) ≠ (nb068AlphaDummy473) from (by
                                  unfold nb068AlphaDummy473;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0486) 0))))
                              (show (nb068AlphaDummy468 f) ≠ (nb068AlphaDummy474 f) from
                                (by
                                  unfold nb068AlphaDummy474;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0487 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0160`. -/
@[expose]
noncomputable def nb068SplitAlpha0160 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
        ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
        ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
        ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
        ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
        ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
        ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy458))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy457)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy457)) (synC1c))
          (Class.cv (nb068AlphaDummy457))))
      (Wff.classEq (Class.cv (nb068AlphaDummy460 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy459 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy459 f)) (synC1c))
          (Class.cv (nb068AlphaDummy459 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy450))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy452 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy464) from (by
                              unfold nb068AlphaDummy464;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0472) 1))))
                          (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy467 f) from (by
                              unfold nb068AlphaDummy467;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0473 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy463) from (by
                                unfold nb068AlphaDummy463;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0472) 0))))
                            (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy466 f) from (by
                                unfold nb068AlphaDummy466;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0473 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                                  unfold nb068AlphaDummy461;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                              (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from
                                (by
                                  unfold nb068AlphaDummy462;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy465), (nb068AlphaDummy468 f)),
                              ((nb068AlphaDummy464), (nb068AlphaDummy467 f)),
                              ((nb068AlphaDummy463), (nb068AlphaDummy466 f)),
                              ((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                              ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                              ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                              ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
                              ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                              ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                              ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                              ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                              ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0159 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                      unfold nb068AlphaDummy461;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                  (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                      unfold nb068AlphaDummy462;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                  ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                  ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                  ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
                  ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                  ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                  ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                  ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                  ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from (by
                    unfold nb068AlphaDummy461;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                    unfold nb068AlphaDummy462;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy457) ≠ (nb068AlphaDummy461) from
                    (by
                      unfold nb068AlphaDummy461;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0470) 0))))
                  (show (nb068AlphaDummy459 f) ≠ (nb068AlphaDummy462 f) from (by
                      unfold nb068AlphaDummy462;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0471 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy461), (nb068AlphaDummy462 f)),
                  ((nb068AlphaDummy457), (nb068AlphaDummy459 f)),
                  ((nb068AlphaDummy458), (nb068AlphaDummy460 f)),
                  ((nb068AlphaDummy483), (nb068AlphaDummy484 f)),
                  ((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                  ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                  ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                  ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                  ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0161`. -/
@[expose]
noncomputable def nb068SplitAlpha0161 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
        ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy479))
          (Class.cab (nb068AlphaDummy449)
            (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
              (Wff.classEq (Class.cv (nb068AlphaDummy449))
                (synCun (synCphi (Class.cv (nb068AlphaDummy450))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy479))
            (Class.cab (nb068AlphaDummy449)
              (synWrex (nb068AlphaDummy450) (Class.cv (nb068AlphaDummy407))
                (Wff.classEq (Class.cv (nb068AlphaDummy449))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy450)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy480 f))
          (Class.cab (nb068AlphaDummy451 f)
            (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy480 f))
            (Class.cab (nb068AlphaDummy451 f)
              (synWrex (nb068AlphaDummy452 f) (Class.cv (nb068AlphaDummy409 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy451 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy452 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy450) from
                    (by
                      unfold nb068AlphaDummy450;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
                  (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy452 f) from (by
                      unfold nb068AlphaDummy452;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0492 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy449) from
                      (by
                        unfold nb068AlphaDummy449;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 0))))
                    (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy451 f) from (by
                        unfold nb068AlphaDummy451;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0492 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy479) from (by
                          unfold nb068AlphaDummy479;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0494) 0))))
                      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy480 f) from (by
                          unfold nb068AlphaDummy480;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0495 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy453) from (by
                            unfold nb068AlphaDummy453;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0491) 0))))
                        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy454 f) from (by
                            unfold nb068AlphaDummy454;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0493 f) 0))))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                          (freshVar_injective (((synCcnv (Class.cv f))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy408))).fv ∪
                      ((Class.cv (nb068AlphaDummy407))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy410 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy409 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy450) ≠
        (nb068AlphaDummy457) from (by
          unfold nb068AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy459 f) from (by
          unfold nb068AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy458) from (by
          unfold nb068AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy460 f) from (by
          unfold nb068AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy483) from (by
          unfold nb068AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy484 f) from (by
          unfold nb068AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy481) from (by
          unfold nb068AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy482 f) from (by
          unfold nb068AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0160 x y f)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy450) ≠
        (nb068AlphaDummy457) from (by
          unfold nb068AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy459 f) from (by
          unfold nb068AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy458) from (by
          unfold nb068AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy460 f) from (by
          unfold nb068AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy483) from (by
          unfold nb068AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy484 f) from (by
          unfold nb068AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy481) from (by
          unfold nb068AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy482 f) from (by
          unfold nb068AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0160 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                          ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                          ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                          ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                          ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy450) from
                      (by
                        unfold nb068AlphaDummy450;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0490) 1))))
                    (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy452 f) from (by
                        unfold nb068AlphaDummy452;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0492 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy449) from (by
                          unfold nb068AlphaDummy449;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0490) 0))))
                      (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy451 f) from (by
                          unfold nb068AlphaDummy451;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0492 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy479) from (by
                            unfold nb068AlphaDummy479;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0494) 0))))
                        (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy480 f) from (by
                            unfold nb068AlphaDummy480;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0495 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy453) from (by
                              unfold nb068AlphaDummy453;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0491) 0))))
                          (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy454 f) from (by
                              unfold nb068AlphaDummy454;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0493 f) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide))
                            (freshVar_injective (((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy408))).fv ∪
                        ((Class.cv (nb068AlphaDummy407))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy410 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy409 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy457) from (by
          unfold nb068AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy459 f) from (by
          unfold nb068AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy458) from (by
          unfold nb068AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy460 f) from (by
          unfold nb068AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy483) from (by
          unfold nb068AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy484 f) from (by
          unfold nb068AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy481)
        from (by
          unfold nb068AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496)
                  0)))) (show (nb068AlphaDummy452 f) ≠ (nb068AlphaDummy482 f) from (by
          unfold nb068AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0160 x y f)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy457) from (by
          unfold nb068AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy459 f) from (by
          unfold nb068AlphaDummy459;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy458) from (by
          unfold nb068AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0468) 1)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy460 f) from (by
          unfold nb068AlphaDummy460;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0469 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy450) ≠ (nb068AlphaDummy483) from (by
          unfold nb068AlphaDummy483;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0498) 0)))) (show (nb068AlphaDummy452 f) ≠
        (nb068AlphaDummy484 f) from (by
          unfold nb068AlphaDummy484;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0499 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy450) ≠ (nb068AlphaDummy481)
        from (by
          unfold nb068AlphaDummy481;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0496)
                  0)))) (show (nb068AlphaDummy452 f) ≠ (nb068AlphaDummy482 f) from (by
          unfold nb068AlphaDummy482;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0497 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (nb068SplitAlpha0160 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy481), (nb068AlphaDummy482 f)),
                            ((nb068AlphaDummy450), (nb068AlphaDummy452 f)),
                            ((nb068AlphaDummy449), (nb068AlphaDummy451 f)),
                            ((nb068AlphaDummy479), (nb068AlphaDummy480 f)),
                            ((nb068AlphaDummy453), (nb068AlphaDummy454 f)),
                            ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                            ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                            ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part056`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0162`. -/
@[expose]
noncomputable def nb068SplitAlpha0162 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0163`. -/
@[expose]
noncomputable def nb068SplitAlpha0163 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy140))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))
          (Class.cv (nb068AlphaDummy139))))
      (Wff.classEq (Class.cv (nb068AlphaDummy142 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))
          (Class.cv (nb068AlphaDummy141 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                              unfold nb068AlphaDummy146;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                          (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
                              unfold nb068AlphaDummy149;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                                unfold nb068AlphaDummy145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                                unfold nb068AlphaDummy148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                                  unfold nb068AlphaDummy143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from
                                (by
                                  unfold nb068AlphaDummy144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                              ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                              ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                              ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                              ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0162 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                    unfold nb068AlphaDummy143;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                    unfold nb068AlphaDummy144;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from
                    (by
                      unfold nb068AlphaDummy143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                  (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                      unfold nb068AlphaDummy144;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                  ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                  ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                  ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                  ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                  ((nb068AlphaDummy137), (nb068AlphaDummy138 f)),
                  ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0164`. -/
@[expose]
noncomputable def nb068SplitAlpha0164 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
        ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
        ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
        ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy145))
            (synCun (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy148 f))
            (synCun (Class.cv (nb068AlphaDummy149 f))
              (Class.cv (nb068AlphaDummy150 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0140) 0))))
                          (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0141 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0138) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0139 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy153) from (by
                              unfold nb068AlphaDummy153;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0144) 0))))
                          (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy154 f) from (by
                              unfold nb068AlphaDummy154;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0145 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy151) from (by
                                unfold nb068AlphaDummy151;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0142) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy152 f) from (by
                                unfold nb068AlphaDummy152;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0143 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
          ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
          ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy157) from (by
                                unfold nb068AlphaDummy157;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0148) 0))))
                            (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy158 f) from (by
                                unfold nb068AlphaDummy158;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0149 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy146) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0146) 0))))
                              (show (nb068AlphaDummy149 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0147 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy159) from (by
                                unfold nb068AlphaDummy159;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0152) 0))))
                            (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy160 f) from (by
                                unfold nb068AlphaDummy160;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0153 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy147) ≠ (nb068AlphaDummy155) from (by
                                  unfold nb068AlphaDummy155;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0150) 0))))
                              (show (nb068AlphaDummy150 f) ≠ (nb068AlphaDummy156 f) from
                                (by
                                  unfold nb068AlphaDummy156;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0151 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0165`. -/
@[expose]
noncomputable def nb068SplitAlpha0165 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
        ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
        ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
        ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
        ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
        ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
        ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
        ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy143))
              (synCplc (Class.cv (nb068AlphaDummy139)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy143)) (Class.cv (nb068AlphaDummy139)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy144 f))
              (synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy144 f))
            (Class.cv (nb068AlphaDummy141 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy146) from (by
                          unfold nb068AlphaDummy146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0136) 1))))
                      (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy149 f) from (by
                          unfold nb068AlphaDummy149;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0137 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy145) from (by
                            unfold nb068AlphaDummy145;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0136) 0))))
                        (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy148 f) from (by
                            unfold nb068AlphaDummy148;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0137 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                              unfold nb068AlphaDummy143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0134) 0))))
                          (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                              unfold nb068AlphaDummy144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy147), (nb068AlphaDummy150 f)),
                          ((nb068AlphaDummy146), (nb068AlphaDummy149 f)),
                          ((nb068AlphaDummy145), (nb068AlphaDummy148 f)),
                          ((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
                          ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
                          ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
                          ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
                          ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0164 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                  unfold nb068AlphaDummy143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                  unfold nb068AlphaDummy144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
              ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
              ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
              ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                unfold nb068AlphaDummy143;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
            (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                unfold nb068AlphaDummy144;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy139) ≠ (nb068AlphaDummy143) from (by
                  unfold nb068AlphaDummy143;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0134) 0))))
              (show (nb068AlphaDummy141 f) ≠ (nb068AlphaDummy144 f) from (by
                  unfold nb068AlphaDummy144;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0135 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy143), (nb068AlphaDummy144 f)),
              ((nb068AlphaDummy139), (nb068AlphaDummy141 f)),
              ((nb068AlphaDummy140), (nb068AlphaDummy142 f)),
              ((nb068AlphaDummy165), (nb068AlphaDummy166 f)),
              ((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
              ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
              ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
              ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
              ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part057`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0166`. -/
@[expose]
noncomputable def nb068SplitAlpha0166 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
        ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy161))
          (Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy161))
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
          (Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb068AlphaDummy162 f))
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                    (by
                      unfold nb068AlphaDummy132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                  (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                      unfold nb068AlphaDummy134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from
                      (by
                        unfold nb068AlphaDummy131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                        unfold nb068AlphaDummy133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 0)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                          unfold nb068AlphaDummy161;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                          unfold nb068AlphaDummy162;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                            unfold nb068AlphaDummy135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                            unfold nb068AlphaDummy136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy125))).fv ∪
                      ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0165 x y f)))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show (nb068AlphaDummy132) ≠
        (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy163) from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                                        (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy132))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb068AlphaDummy134 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                      (TAlphaClass.cab (nb068SplitAlpha0165 x y f)))))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                          ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                          ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                          ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                          ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from
                      (by
                        unfold nb068AlphaDummy132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
                    (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
                        unfold nb068AlphaDummy134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0156 f) 1)))) (TAlphaVar.there
                      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
                          unfold nb068AlphaDummy131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0154) 0))))
                      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
                          unfold nb068AlphaDummy133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy161) from (by
                            unfold nb068AlphaDummy161;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0158) 0))))
                        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy162 f) from (by
                            unfold nb068AlphaDummy162;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy135) from (by
                              unfold nb068AlphaDummy135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0155) 0))))
                          (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy136 f) from (by
                              unfold nb068AlphaDummy136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb068AlphaDummy125))).fv ∪
                        ((Class.cv (nb068AlphaDummy126))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb068AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0165 x y f)))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy165) from (by
          unfold nb068AlphaDummy165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0162) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy166 f) from (by
          unfold nb068AlphaDummy166;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0163 f)
                  0)))) (TAlphaVar.there (show (nb068AlphaDummy132) ≠ (nb068AlphaDummy163)
        from (by
          unfold nb068AlphaDummy163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0160)
                  0)))) (show (nb068AlphaDummy134 f) ≠ (nb068AlphaDummy164 f) from (by
          unfold nb068AlphaDummy164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0161 f)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy132))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb068AlphaDummy134 f))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
        (nb068SplitAlpha0165 x y f)))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb068AlphaDummy163), (nb068AlphaDummy164 f)),
                            ((nb068AlphaDummy132), (nb068AlphaDummy134 f)),
                            ((nb068AlphaDummy131), (nb068AlphaDummy133 f)),
                            ((nb068AlphaDummy161), (nb068AlphaDummy162 f)),
                            ((nb068AlphaDummy135), (nb068AlphaDummy136 f)),
                            ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                            ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                            ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                            ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                            ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                            ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                            ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                            ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                            ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                            ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                            ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                            ((nb068AlphaDummy001), x),
                            ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0167`. -/
@[expose]
noncomputable def nb068SplitAlpha0167 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0168`. -/
@[expose]
noncomputable def nb068SplitAlpha0168 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classEq (Class.cv (nb068AlphaDummy176))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))
          (Class.cv (nb068AlphaDummy175))))
      (Wff.classEq (Class.cv (nb068AlphaDummy178 f))
        (synCif (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))
          (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))
          (Class.cv (nb068AlphaDummy177 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
        (freshVar_injective (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                              unfold nb068AlphaDummy182;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                          (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
                              unfold nb068AlphaDummy185;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                                unfold nb068AlphaDummy181;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                                unfold nb068AlphaDummy184;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                                  unfold nb068AlphaDummy179;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from
                                (by
                                  unfold nb068AlphaDummy180;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                              (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfClosed
                            [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                              ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                              ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                              ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                              ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                              ((nb068AlphaDummy001), x),
                              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                            (synC1c) (by simp only [fv_syn_c1c])))
                        (TAlphaWff.neg (nb068SplitAlpha0167 x y f)))))))) (TAlphaWff.classMem
              (TAlphaClass.cv (TAlphaVar.there
                  (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                  ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                    unfold nb068AlphaDummy179;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                    unfold nb068AlphaDummy180;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from
                    (by
                      unfold nb068AlphaDummy179;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                  (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                      unfold nb068AlphaDummy180;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                  ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                  ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                  ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                  ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                  ((nb068AlphaDummy173), (nb068AlphaDummy174 f)),
                  ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                  ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                  ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                  ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                  ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                  ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                  ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                  ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                  ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                  ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                  ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                  ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                  ((nb068AlphaDummy001), x),
                  ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                (synCnnc) (by simp only [fv_syn_cnnc]))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part058`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0169`. -/
@[expose]
noncomputable def nb068SplitAlpha0169 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
        ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
        ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
        ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb068AlphaDummy181))
            (synCun (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb068AlphaDummy184 f))
            (synCun (Class.cv (nb068AlphaDummy185 f))
              (Class.cv (nb068AlphaDummy186 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0178) 0))))
                          (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0176) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0177 f) 0))))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy189) from (by
                              unfold nb068AlphaDummy189;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0182) 0))))
                          (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy190 f) from (by
                              unfold nb068AlphaDummy190;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0183 f) 0))))
                          (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy187) from (by
                                unfold nb068AlphaDummy187;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0180) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy188 f) from (by
                                unfold nb068AlphaDummy188;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0181 f) 0))))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
          ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
          ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
          ((nb068AlphaDummy001), x),
          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy193) from (by
                                unfold nb068AlphaDummy193;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0186) 0))))
                            (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy194 f) from (by
                                unfold nb068AlphaDummy194;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0187 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy182) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0184) 0))))
                              (show (nb068AlphaDummy185 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0185 f) 0))))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy195) from (by
                                unfold nb068AlphaDummy195;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0190) 0))))
                            (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy196 f) from (by
                                unfold nb068AlphaDummy196;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb068_support_mem_0191 f) 0))))
                            (TAlphaVar.there
                              (show (nb068AlphaDummy183) ≠ (nb068AlphaDummy191) from (by
                                  unfold nb068AlphaDummy191;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0188) 0))))
                              (show (nb068AlphaDummy186 f) ≠ (nb068AlphaDummy192 f) from
                                (by
                                  unfold nb068AlphaDummy192;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb068_support_mem_0189 f) 0))))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0170`. -/
@[expose]
noncomputable def nb068SplitAlpha0170 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
        ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
        ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
        ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
        ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
        ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy179))
              (synCplc (Class.cv (nb068AlphaDummy175)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy179)) (Class.cv (nb068AlphaDummy175)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc)))))
      (Wff.imp (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
              (synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c)))
            (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc)))) (synWa
          (Wff.classMem (Class.cv (nb068AlphaDummy180 f))
            (Class.cv (nb068AlphaDummy177 f)))
          (Wff.neg (Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))))) :=
  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there
                      (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy182) from (by
                          unfold nb068AlphaDummy182;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0174) 1))))
                      (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy185 f) from (by
                          unfold nb068AlphaDummy185;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0175 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy181) from (by
                            unfold nb068AlphaDummy181;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0174) 0))))
                        (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy184 f) from (by
                            unfold nb068AlphaDummy184;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0175 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                              unfold nb068AlphaDummy179;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0172) 0))))
                          (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                              unfold nb068AlphaDummy180;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
                          (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb068AlphaDummy183), (nb068AlphaDummy186 f)),
                          ((nb068AlphaDummy182), (nb068AlphaDummy185 f)),
                          ((nb068AlphaDummy181), (nb068AlphaDummy184 f)),
                          ((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
                          ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
                          ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
                          ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
                          ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                          ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                          ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                          ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                          ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                          ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                          ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                          ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                          ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                          ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                          ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                          ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                          ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                          ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                          ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                          ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                          ((nb068AlphaDummy001), x),
                          ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                        (synC1c) (by simp only [fv_syn_c1c])))
                    (TAlphaWff.neg (nb068SplitAlpha0169 x y f)))))))) (TAlphaWff.classMem
          (TAlphaClass.cv (TAlphaVar.there
              (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
              ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
              ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
              ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
          (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                unfold nb068AlphaDummy179;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
            (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                unfold nb068AlphaDummy180;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
            (TAlphaVar.there (show (nb068AlphaDummy175) ≠ (nb068AlphaDummy179) from (by
                  unfold nb068AlphaDummy179;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0172) 0))))
              (show (nb068AlphaDummy177 f) ≠ (nb068AlphaDummy180 f) from (by
                  unfold nb068AlphaDummy180;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0173 f) 0))))
              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
            [((nb068AlphaDummy179), (nb068AlphaDummy180 f)),
              ((nb068AlphaDummy175), (nb068AlphaDummy177 f)),
              ((nb068AlphaDummy176), (nb068AlphaDummy178 f)),
              ((nb068AlphaDummy201), (nb068AlphaDummy202 f)),
              ((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
              ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
              ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
              ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
              ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
              ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
              ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
              ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
              ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
              ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
              ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
              ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
              ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
              ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
              ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
              ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
              ((nb068AlphaDummy001), x),
              ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
            (synCnnc) (by simp only [fv_syn_cnnc]))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0171`. -/
@[expose]
noncomputable def nb068SplitAlpha0171 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
        ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
        ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
        ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
        ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy168))
            (Class.cv (nb068AlphaDummy125))) (Wff.classEq (Class.cv (nb068AlphaDummy167))
            (synCun (synCphi (Class.cv (nb068AlphaDummy168))) (synCsn (synC0c))))))
      (Wff.neg (synWa (Wff.classMem (Class.cv (nb068AlphaDummy170 f))
            (Class.cv (nb068AlphaDummy127 f)))
          (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
            (synCun (synCphi (Class.cv (nb068AlphaDummy170 f))) (synCsn (synC0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there
            (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from (by
                unfold nb068AlphaDummy168;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
            (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
                unfold nb068AlphaDummy170;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
            (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
                  unfold nb068AlphaDummy167;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
              (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
                  unfold nb068AlphaDummy169;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
              (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy197) from (by
                    unfold nb068AlphaDummy197;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0196) 0))))
                (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy198 f) from (by
                    unfold nb068AlphaDummy198;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0197 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy171) from
                    (by
                      unfold nb068AlphaDummy171;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0193) 0))))
                  (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy172 f) from (by
                      unfold nb068AlphaDummy172;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0195 f) 0))))
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy000))).fv)
                      (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                    (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb068AlphaDummy126))).fv ∪
                ((Class.cv (nb068AlphaDummy125))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0170 x y f)))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy168) ≠ (nb068AlphaDummy175) from (by
                                        unfold nb068AlphaDummy175;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0170)
                                                0)))) (show (nb068AlphaDummy170 f) ≠
                                        (nb068AlphaDummy177 f) from (by
                                        unfold nb068AlphaDummy177;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0171 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from
                                        (by
                                          unfold nb068AlphaDummy176;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0170)
                                                  1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
                                          unfold nb068AlphaDummy178;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0171 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy201) from (by
          unfold nb068AlphaDummy201;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0200) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy202 f) from (by
          unfold nb068AlphaDummy202;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0201 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy199) from (by
          unfold nb068AlphaDummy199;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0198) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy200 f) from (by
          unfold nb068AlphaDummy200;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0199 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy168))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy170 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))
                                (TAlphaClass.cab (nb068SplitAlpha0170 x y f)))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfClosed
                  [((nb068AlphaDummy199), (nb068AlphaDummy200 f)),
                    ((nb068AlphaDummy168), (nb068AlphaDummy170 f)),
                    ((nb068AlphaDummy167), (nb068AlphaDummy169 f)),
                    ((nb068AlphaDummy197), (nb068AlphaDummy198 f)),
                    ((nb068AlphaDummy171), (nb068AlphaDummy172 f)),
                    ((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
                    ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
                    ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
                    ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
                    ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
                    ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
                    ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
                    ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
                    ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
                    ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
                    ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
                    ((nb068AlphaDummy001), x),
                    ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
                  (synCcompl (synCsn (synC0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0172`. -/
@[expose]
noncomputable def nb068SplitAlpha0172 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy126), (nb068AlphaDummy128 f)),
        ((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.classMem
        (synCop (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy125)))
        (Class.cv (nb068AlphaDummy000)))
      (Wff.classMem (synCop (Class.cv (nb068AlphaDummy128 f))
          (Class.cv (nb068AlphaDummy127 f))) (Class.cv f)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0168 x y f)))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
                                    unfold nb068AlphaDummy168;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0164) 1)))) (show
                                  (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
                                    unfold nb068AlphaDummy170;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb068_support_mem_0166 f)
                                            1)))) (TAlphaVar.there
                                  (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from
                                    (by
                                      unfold nb068AlphaDummy167;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0164)
                                              0)))) (show
                                    (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from
                                    (by
                                      unfold nb068AlphaDummy169;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0166 f)
                                              0)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy126) ≠ (nb068AlphaDummy173) from (by
                                        unfold nb068AlphaDummy173;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0168)
                                                0)))) (show (nb068AlphaDummy128 f) ≠
                                        (nb068AlphaDummy174 f) from (by
                                        unfold nb068AlphaDummy174;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0169 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy126) ≠ (nb068AlphaDummy171) from
                                        (by
                                          unfold nb068AlphaDummy171;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0165)
                                                  0)))) (show (nb068AlphaDummy128 f) ≠
        (nb068AlphaDummy172 f) from (by
                                          unfold nb068AlphaDummy172;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0167 f) 0))))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb068AlphaDummy126))).fv ∪
                                    ((Class.cv (nb068AlphaDummy125))).fv) (by decide))
                                (freshVar_injective (((Class.cv (nb068AlphaDummy128 f))).fv ∪
                                    ((Class.cv (nb068AlphaDummy127 f))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (show (nb068AlphaDummy168) ≠
        (nb068AlphaDummy175) from (by
          unfold nb068AlphaDummy175;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 0)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy177 f) from (by
          unfold nb068AlphaDummy177;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy168) ≠ (nb068AlphaDummy176) from (by
          unfold nb068AlphaDummy176;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0170) 1)))) (show (nb068AlphaDummy170 f) ≠
        (nb068AlphaDummy178 f) from (by
          unfold nb068AlphaDummy178;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0171 f) 1)))) (TAlphaVar.here _ _ _)))))
                                  (nb068SplitAlpha0168 x y f)))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb068SplitAlpha0171 x y f)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.neg (TAlphaWff.all (nb068SplitAlpha0171 x y f))))))))))))
    (TAlphaClass.cv (TAlphaVar.there
        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy126) from (by
            unfold nb068AlphaDummy126;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 1))))
        (show f ≠ (nb068AlphaDummy128 f) from (by
            unfold nb068AlphaDummy128;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 1))))
        (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy125) from (by
              unfold nb068AlphaDummy125;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0212) 0))))
          (show f ≠ (nb068AlphaDummy127 f) from (by
              unfold nb068AlphaDummy127;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0213 f) 0))))
          (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy129) from (by
                unfold nb068AlphaDummy129;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0210) 0))))
            (show f ≠ (nb068AlphaDummy130 f) from (by
                unfold nb068AlphaDummy130;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0211 f) 0))))
            (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy408) from (by
                  unfold nb068AlphaDummy408;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0510) 1))))
              (show f ≠ (nb068AlphaDummy410 f) from (by
                  unfold nb068AlphaDummy410;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0511 f) 1))))
              (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy407) from (by
                    unfold nb068AlphaDummy407;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0510) 0))))
                (show f ≠ (nb068AlphaDummy409 f) from (by
                    unfold nb068AlphaDummy409;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0511 f) 0))))
                (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy411) from
                    (by
                      unfold nb068AlphaDummy411;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0508) 0))))
                  (show f ≠ (nb068AlphaDummy412 f) from (by
                      unfold nb068AlphaDummy412;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0509 f) 0))))
                  (TAlphaVar.there (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy329) from
                      (by
                        unfold nb068AlphaDummy329;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0504) 2))))
                    (show f ≠ (nb068AlphaDummy332 f) from (by
                        unfold nb068AlphaDummy332;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb068_support_mem_0506 f) 2)))) (TAlphaVar.there
                      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy328) from (by
                          unfold nb068AlphaDummy328;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0504) 1))))
                      (show f ≠ (nb068AlphaDummy331 f) from (by
                          unfold nb068AlphaDummy331;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb068_support_mem_0506 f) 1))))
                      (TAlphaVar.there
                        (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy327) from (by
                            unfold nb068AlphaDummy327;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0504) 0))))
                        (show f ≠ (nb068AlphaDummy330 f) from (by
                            unfold nb068AlphaDummy330;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb068_support_mem_0506 f) 0))))
                        (TAlphaVar.there
                          (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy333) from (by
                              unfold nb068AlphaDummy333;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0505) 0))))
                          (show f ≠ (nb068AlphaDummy334 f) from (by
                              unfold nb068AlphaDummy334;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb068_support_mem_0507 f) 0))))
                          (TAlphaVar.here _ _ _)))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0173`. -/
@[expose]
noncomputable def nb068SplitAlpha0173 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy125), (nb068AlphaDummy127 f)),
        ((nb068AlphaDummy129), (nb068AlphaDummy130 f)),
        ((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.all (nb068AlphaDummy126) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy129))
              (synCop (Class.cv (nb068AlphaDummy125)) (Class.cv (nb068AlphaDummy126))))
            (synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
              (Class.cv (nb068AlphaDummy125))))))
      (Wff.all (nb068AlphaDummy128 f) (Wff.neg (synWa
            (Wff.classEq (Class.cv (nb068AlphaDummy130 f))
              (synCop (Class.cv (nb068AlphaDummy127 f))
                (Class.cv (nb068AlphaDummy128 f))))
            (synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
              (Class.cv (nb068AlphaDummy127 f)))))) :=
  (TAlphaWff.all (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (Ne.symm
                (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy129) from (by
                    unfold nb068AlphaDummy129;
                    with_reducible
                      exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0124) 0)))))
              (Ne.symm (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy130 f) from (by
                    unfold nb068AlphaDummy130;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0125 f) 0)))))
              (TAlphaVar.there (Ne.symm
                  (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy129) from (by
                      unfold nb068AlphaDummy129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0122) 0)))))
                (Ne.symm (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy130 f) from (by
                      unfold nb068AlphaDummy130;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0123 f) 0)))))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0163 x y f)))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from
                                        (by
                                          unfold nb068AlphaDummy132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0126)
                                                  1)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy134 f) from (by
                                          unfold nb068AlphaDummy134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0128 f) 1))))
                                      (TAlphaVar.there (show (nb068AlphaDummy125) ≠
        (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0126) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0128 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy137) from (by
          unfold nb068AlphaDummy137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0130) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy138 f) from (by
          unfold nb068AlphaDummy138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0131 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy125) ≠ (nb068AlphaDummy135) from (by
          unfold nb068AlphaDummy135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0127) 0)))) (show (nb068AlphaDummy127 f) ≠
        (nb068AlphaDummy136 f) from (by
          unfold nb068AlphaDummy136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0129 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb068AlphaDummy000))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                      (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy125))).fv ∪
        ((Class.cv (nb068AlphaDummy126))).fv) (by decide)) (freshVar_injective
                                        (((Class.cv (nb068AlphaDummy127 f))).fv ∪
        ((Class.cv (nb068AlphaDummy128 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy139) from (by
          unfold nb068AlphaDummy139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 0)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy141 f) from (by
          unfold nb068AlphaDummy141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy132) ≠ (nb068AlphaDummy140) from (by
          unfold nb068AlphaDummy140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0132) 1)))) (show (nb068AlphaDummy134 f) ≠
        (nb068AlphaDummy142 f) from (by
          unfold nb068AlphaDummy142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0133 f)
                  1)))) (TAlphaVar.here _ _ _))))) (nb068SplitAlpha0163 x y f)))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0166 x y f)))))))))
        (nb068SplitAlpha0172 x y f))))

/-- Checked nominal proof certificate identified upstream as `nb068_split_alpha_0174`. -/
@[expose]
noncomputable def nb068SplitAlpha0174 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb068AlphaDummy408), (nb068AlphaDummy410 f)),
        ((nb068AlphaDummy407), (nb068AlphaDummy409 f)),
        ((nb068AlphaDummy411), (nb068AlphaDummy412 f)),
        ((nb068AlphaDummy329), (nb068AlphaDummy332 f)),
        ((nb068AlphaDummy328), (nb068AlphaDummy331 f)),
        ((nb068AlphaDummy327), (nb068AlphaDummy330 f)),
        ((nb068AlphaDummy333), (nb068AlphaDummy334 f)),
        ((nb068AlphaDummy000), f), ((nb068AlphaDummy002), y),
        ((nb068AlphaDummy001), x),
        ((nb068AlphaDummy003), (nb068AlphaDummy004 x y f))]
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy411))
          (synCop (Class.cv (nb068AlphaDummy407)) (Class.cv (nb068AlphaDummy408))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy408))
            (synCcnv (Class.cv (nb068AlphaDummy000))) (Class.cv (nb068AlphaDummy407)))))
      (Wff.imp (Wff.classEq (Class.cv (nb068AlphaDummy412 f))
          (synCop (Class.cv (nb068AlphaDummy409 f)) (Class.cv (nb068AlphaDummy410 f))))
        (Wff.neg (synWbr (Class.cv (nb068AlphaDummy410 f)) (synCcnv (Class.cv f))
            (Class.cv (nb068AlphaDummy409 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (Ne.symm
            (show (nb068AlphaDummy408) ≠ (nb068AlphaDummy411) from (by
                unfold nb068AlphaDummy411;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0422) 0))))) (Ne.symm
            (show (nb068AlphaDummy410 f) ≠ (nb068AlphaDummy412 f) from (by
                unfold nb068AlphaDummy412;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0423 f) 0)))))
          (TAlphaVar.there (Ne.symm (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy411) from
                (by
                  unfold nb068AlphaDummy411;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0420) 0)))))
            (Ne.symm (show (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy412 f) from (by
                  unfold nb068AlphaDummy412;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0421 f) 0)))))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy414) from
                                    (by
                                      unfold nb068AlphaDummy414;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0424)
                                              1)))) (show
                                    (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy416 f) from
                                    (by
                                      unfold nb068AlphaDummy416;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0426 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy407) ≠ (nb068AlphaDummy413) from (by
                                        unfold nb068AlphaDummy413;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0424)
                                                0)))) (show (nb068AlphaDummy409 f) ≠
                                        (nb068AlphaDummy415 f) from (by
                                        unfold nb068AlphaDummy415;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0426 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy407) ≠ (nb068AlphaDummy419) from
                                        (by
                                          unfold nb068AlphaDummy419;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0428)
                                                  0)))) (show (nb068AlphaDummy409 f) ≠
        (nb068AlphaDummy420 f) from (by
                                          unfold nb068AlphaDummy420;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0429 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy407) ≠
        (nb068AlphaDummy417) from (by
          unfold nb068AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0425) 0)))) (show (nb068AlphaDummy409 f) ≠
        (nb068AlphaDummy418 f) from (by
          unfold nb068AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0427 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy407))).fv ∪
                                      ((Class.cv (nb068AlphaDummy408))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy409 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy410 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0153 x y f)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb068AlphaDummy407) ≠ (nb068AlphaDummy414) from
                                    (by
                                      unfold nb068AlphaDummy414;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0424)
                                              1)))) (show
                                    (nb068AlphaDummy409 f) ≠ (nb068AlphaDummy416 f) from
                                    (by
                                      unfold nb068AlphaDummy416;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb068_support_mem_0426 f)
                                              1)))) (TAlphaVar.there (show
                                      (nb068AlphaDummy407) ≠ (nb068AlphaDummy413) from (by
                                        unfold nb068AlphaDummy413;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0424)
                                                0)))) (show (nb068AlphaDummy409 f) ≠
                                        (nb068AlphaDummy415 f) from (by
                                        unfold nb068AlphaDummy415;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0426 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy407) ≠ (nb068AlphaDummy419) from
                                        (by
                                          unfold nb068AlphaDummy419;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0428)
                                                  0)))) (show (nb068AlphaDummy409 f) ≠
        (nb068AlphaDummy420 f) from (by
                                          unfold nb068AlphaDummy420;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0429 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy407) ≠
        (nb068AlphaDummy417) from (by
          unfold nb068AlphaDummy417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0425) 0)))) (show (nb068AlphaDummy409 f) ≠
        (nb068AlphaDummy418 f) from (by
          unfold nb068AlphaDummy418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0427 f) 0)))) (TAlphaVar.there (freshVar_injective
        (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) (by decide)) (freshVar_injective
        (((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb068AlphaDummy407))).fv ∪
                                      ((Class.cv (nb068AlphaDummy408))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb068AlphaDummy409 f))).fv ∪
                                      ((Class.cv (nb068AlphaDummy410 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb068SplitAlpha0153 x y f)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0156 x y f)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy408) ≠ (nb068AlphaDummy450) from (by
                                        unfold nb068AlphaDummy450;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0462)
                                                1)))) (show (nb068AlphaDummy410 f) ≠
                                        (nb068AlphaDummy452 f) from (by
                                        unfold nb068AlphaDummy452;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0464 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy408) ≠ (nb068AlphaDummy449) from
                                        (by
                                          unfold nb068AlphaDummy449;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0462)
                                                  0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy451 f) from (by
                                          unfold nb068AlphaDummy451;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0464 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy408) ≠
        (nb068AlphaDummy455) from (by
          unfold nb068AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0466) 0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy456 f) from (by
          unfold nb068AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0467 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy408) ≠ (nb068AlphaDummy453) from (by
          unfold nb068AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0463) 0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy454 f) from (by
          unfold nb068AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0465 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy408))).fv ∪
                                        ((Class.cv (nb068AlphaDummy407))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy410 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy409 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0158 x y f)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb068AlphaDummy408) ≠ (nb068AlphaDummy450) from (by
                                        unfold nb068AlphaDummy450;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0462)
                                                1)))) (show (nb068AlphaDummy410 f) ≠
                                        (nb068AlphaDummy452 f) from (by
                                        unfold nb068AlphaDummy452;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb068_support_mem_0464 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb068AlphaDummy408) ≠ (nb068AlphaDummy449) from
                                        (by
                                          unfold nb068AlphaDummy449;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb068_support_mem_0462)
                                                  0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy451 f) from (by
                                          unfold nb068AlphaDummy451;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb068_support_mem_0464 f) 0))))
                                      (TAlphaVar.there (show (nb068AlphaDummy408) ≠
        (nb068AlphaDummy455) from (by
          unfold nb068AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0466) 0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy456 f) from (by
          unfold nb068AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0467 f) 0)))) (TAlphaVar.there (show
        (nb068AlphaDummy408) ≠ (nb068AlphaDummy453) from (by
          unfold nb068AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0463) 0)))) (show (nb068AlphaDummy410 f) ≠
        (nb068AlphaDummy454 f) from (by
          unfold nb068AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb068_support_mem_0465 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy408))).fv ∪
                                        ((Class.cv (nb068AlphaDummy407))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb068AlphaDummy410 f))).fv ∪
                                        ((Class.cv (nb068AlphaDummy409 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb068SplitAlpha0158 x y f)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb068SplitAlpha0161 x y f))))))))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.neg (nb068SplitAlpha0173 x y f)))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
