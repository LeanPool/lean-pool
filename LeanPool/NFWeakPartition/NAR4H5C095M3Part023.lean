/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part022

/-! NF weak partition development: NAR4H5C095M3Part023. -/


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

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0040`. -/
@[expose]
noncomputable def nb095SplitAlpha0040 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u),
        ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095AlphaDummy461 D R S_cls E))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095AlphaDummy462 f))
        (synCcompl (synCphi (Class.cv (nb095AlphaDummy432 f))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                            (nb095AlphaDummy437 D R S_cls E) from (by
                            unfold nb095AlphaDummy437;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0438 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy439 f) from (by
                            unfold nb095AlphaDummy439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                              (nb095AlphaDummy438 D R S_cls E) from (by
                              unfold nb095AlphaDummy438;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0438 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy440 f) from (by
                              unfold nb095AlphaDummy440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                                (nb095AlphaDummy463 D R S_cls E) from (by
                                unfold nb095AlphaDummy463;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0468 D R S_cls E) 0))))
                            (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy464 f) from (by
                                unfold nb095AlphaDummy464;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0469 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                                  (nb095AlphaDummy461 D R S_cls E) from (by
                                  unfold nb095AlphaDummy461;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0466 D R S_cls E) 0))))
                              (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy462 f) from
                                (by
                                  unfold nb095AlphaDummy462;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0467 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy432 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy444 D R S_cls E) from (by
          unfold nb095AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R S_cls E)
                  1)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy447 f) from (by
          unfold nb095AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy443 D R S_cls E) from (by
          unfold nb095AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy446 f) from (by
          unfold nb095AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy441 D R S_cls E) from (by
          unfold nb095AlphaDummy441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from (by
          unfold nb095AlphaDummy442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy445 D R S_cls E), (nb095AlphaDummy448 f)),
        ((nb095AlphaDummy444 D R S_cls E), (nb095AlphaDummy447 f)),
        ((nb095AlphaDummy443 D R S_cls E), (nb095AlphaDummy446 f)),
        ((nb095AlphaDummy441 D R S_cls E), (nb095AlphaDummy442 f)),
        ((nb095AlphaDummy437 D R S_cls E), (nb095AlphaDummy439 f)),
        ((nb095AlphaDummy438 D R S_cls E), (nb095AlphaDummy440 f)),
        ((nb095AlphaDummy463 D R S_cls E), (nb095AlphaDummy464 f)),
        ((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy445 D R S_cls E), (nb095AlphaDummy448 f)),
        ((nb095AlphaDummy444 D R S_cls E), (nb095AlphaDummy447 f)),
        ((nb095AlphaDummy443 D R S_cls E), (nb095AlphaDummy446 f)),
        ((nb095AlphaDummy441 D R S_cls E), (nb095AlphaDummy442 f)),
        ((nb095AlphaDummy437 D R S_cls E), (nb095AlphaDummy439 f)),
        ((nb095AlphaDummy438 D R S_cls E), (nb095AlphaDummy440 f)),
        ((nb095AlphaDummy463 D R S_cls E), (nb095AlphaDummy464 f)),
        ((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy444 D
        R S_cls E) ≠ (nb095AlphaDummy455 D R S_cls E) from (by
          unfold
            nb095AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy456 f) from (by
          unfold
            nb095AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy455
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy456 f) from (by
          unfold
            nb095AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy445 D
        R S_cls E) ≠ (nb095AlphaDummy457 D R S_cls E) from (by
          unfold
            nb095AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy458 f) from (by
          unfold
            nb095AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy445 D
        R S_cls E) ≠ (nb095AlphaDummy457 D R S_cls E) from (by
          unfold
            nb095AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy458 f) from (by
          unfold
            nb095AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy437 D R S_cls E) ≠
                                      (nb095AlphaDummy441 D R S_cls E) from (by
                                      unfold nb095AlphaDummy441;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from
                                    (by
                                      unfold nb095AlphaDummy442;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0441 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy441 D R S_cls E),
                                    (nb095AlphaDummy442 f)),
                                  ((nb095AlphaDummy437 D R S_cls E),
                                    (nb095AlphaDummy439 f)),
                                  ((nb095AlphaDummy438 D R S_cls E),
                                    (nb095AlphaDummy440 f)),
                                  ((nb095AlphaDummy463 D R S_cls E),
                                    (nb095AlphaDummy464 f)),
                                  ((nb095AlphaDummy461 D R S_cls E),
                                    (nb095AlphaDummy462 f)),
                                  ((nb095AlphaDummy430 D R S_cls E),
                                    (nb095AlphaDummy432 f)),
                                  ((nb095AlphaDummy429 D R S_cls E),
                                    (nb095AlphaDummy431 f)),
                                  ((nb095AlphaDummy459 D R S_cls E),
                                    (nb095AlphaDummy460 f)),
                                  ((nb095AlphaDummy433 D R S_cls E),
                                    (nb095AlphaDummy434 f)),
                                  ((nb095AlphaDummy387 D R S_cls E),
                                    (nb095AlphaDummy390 f)),
                                  ((nb095AlphaDummy386 D R S_cls E),
                                    (nb095AlphaDummy389 f)),
                                  ((nb095AlphaDummy385 D R S_cls E),
                                    (nb095AlphaDummy388 f)),
                                  ((nb095AlphaDummy391 D R S_cls E),
                                    (nb095AlphaDummy392 f)),
                                  ((nb095AlphaDummy383 D R S_cls E),
                                    (nb095AlphaDummy384 f)),
                                  ((nb095AlphaDummy381 D R S_cls E),
                                    (nb095AlphaDummy382 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095AlphaDummy437 D R S_cls E) ≠
                                    (nb095AlphaDummy441 D R S_cls E) from (by
                                    unfold nb095AlphaDummy441;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from (by
                                    unfold nb095AlphaDummy442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0441 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy437 D R S_cls E) ≠
                                      (nb095AlphaDummy441 D R S_cls E) from (by
                                      unfold nb095AlphaDummy441;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from
                                    (by
                                      unfold nb095AlphaDummy442;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0441 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy441 D R S_cls E),
                                    (nb095AlphaDummy442 f)),
                                  ((nb095AlphaDummy437 D R S_cls E),
                                    (nb095AlphaDummy439 f)),
                                  ((nb095AlphaDummy438 D R S_cls E),
                                    (nb095AlphaDummy440 f)),
                                  ((nb095AlphaDummy463 D R S_cls E),
                                    (nb095AlphaDummy464 f)),
                                  ((nb095AlphaDummy461 D R S_cls E),
                                    (nb095AlphaDummy462 f)),
                                  ((nb095AlphaDummy430 D R S_cls E),
                                    (nb095AlphaDummy432 f)),
                                  ((nb095AlphaDummy429 D R S_cls E),
                                    (nb095AlphaDummy431 f)),
                                  ((nb095AlphaDummy459 D R S_cls E),
                                    (nb095AlphaDummy460 f)),
                                  ((nb095AlphaDummy433 D R S_cls E),
                                    (nb095AlphaDummy434 f)),
                                  ((nb095AlphaDummy387 D R S_cls E),
                                    (nb095AlphaDummy390 f)),
                                  ((nb095AlphaDummy386 D R S_cls E),
                                    (nb095AlphaDummy389 f)),
                                  ((nb095AlphaDummy385 D R S_cls E),
                                    (nb095AlphaDummy388 f)),
                                  ((nb095AlphaDummy391 D R S_cls E),
                                    (nb095AlphaDummy392 f)),
                                  ((nb095AlphaDummy383 D R S_cls E),
                                    (nb095AlphaDummy384 f)),
                                  ((nb095AlphaDummy381 D R S_cls E),
                                    (nb095AlphaDummy382 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                            (nb095AlphaDummy437 D R S_cls E) from (by
                            unfold nb095AlphaDummy437;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0438 D R S_cls E)
                                    0))))
                        (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy439 f) from (by
                            unfold nb095AlphaDummy439;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                        (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                              (nb095AlphaDummy438 D R S_cls E) from (by
                              unfold nb095AlphaDummy438;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0438 D R S_cls E)
                                      1))))
                          (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy440 f) from (by
                              unfold nb095AlphaDummy440;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                          (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                                (nb095AlphaDummy463 D R S_cls E) from (by
                                unfold nb095AlphaDummy463;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0468 D R S_cls E) 0))))
                            (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy464 f) from (by
                                unfold nb095AlphaDummy464;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0469 f) 0))))
                            (TAlphaVar.there (show (nb095AlphaDummy430 D R S_cls E) ≠
                                  (nb095AlphaDummy461 D R S_cls E) from (by
                                  unfold nb095AlphaDummy461;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0466 D R S_cls E) 0))))
                              (show (nb095AlphaDummy432 f) ≠ (nb095AlphaDummy462 f) from
                                (by
                                  unfold nb095AlphaDummy462;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0467 f) 0))))
                              (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095AlphaDummy430 D R S_cls E))).fv) (by decide))
                        (freshVar_injective (((Class.cv (nb095AlphaDummy432 f))).fv)
                          (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy444 D R S_cls E) from (by
          unfold nb095AlphaDummy444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R S_cls E)
                  1)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy447 f) from (by
          unfold nb095AlphaDummy447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy443 D R S_cls E) from (by
          unfold nb095AlphaDummy443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy446 f) from (by
          unfold nb095AlphaDummy446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 0)))) (TAlphaVar.there (show
        (nb095AlphaDummy437 D R S_cls E) ≠ (nb095AlphaDummy441 D R S_cls E) from (by
          unfold nb095AlphaDummy441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from (by
          unfold nb095AlphaDummy442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                      (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy445 D R S_cls E), (nb095AlphaDummy448 f)),
        ((nb095AlphaDummy444 D R S_cls E), (nb095AlphaDummy447 f)),
        ((nb095AlphaDummy443 D R S_cls E), (nb095AlphaDummy446 f)),
        ((nb095AlphaDummy441 D R S_cls E), (nb095AlphaDummy442 f)),
        ((nb095AlphaDummy437 D R S_cls E), (nb095AlphaDummy439 f)),
        ((nb095AlphaDummy438 D R S_cls E), (nb095AlphaDummy440 f)),
        ((nb095AlphaDummy463 D R S_cls E), (nb095AlphaDummy464 f)),
        ((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠ (nb095AlphaDummy451
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy452 f) from (by
          unfold
            nb095AlphaDummy452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy449 D R S_cls E) from (by
          unfold
            nb095AlphaDummy449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy450 f) from (by
          unfold
            nb095AlphaDummy450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb095AlphaDummy445 D R S_cls E), (nb095AlphaDummy448 f)),
        ((nb095AlphaDummy444 D R S_cls E), (nb095AlphaDummy447 f)),
        ((nb095AlphaDummy443 D R S_cls E), (nb095AlphaDummy446 f)),
        ((nb095AlphaDummy441 D R S_cls E), (nb095AlphaDummy442 f)),
        ((nb095AlphaDummy437 D R S_cls E), (nb095AlphaDummy439 f)),
        ((nb095AlphaDummy438 D R S_cls E), (nb095AlphaDummy440 f)),
        ((nb095AlphaDummy463 D R S_cls E), (nb095AlphaDummy464 f)),
        ((nb095AlphaDummy461 D R S_cls E), (nb095AlphaDummy462 f)),
        ((nb095AlphaDummy430 D R S_cls E), (nb095AlphaDummy432 f)),
        ((nb095AlphaDummy429 D R S_cls E), (nb095AlphaDummy431 f)),
        ((nb095AlphaDummy459 D R S_cls E), (nb095AlphaDummy460 f)),
        ((nb095AlphaDummy433 D R S_cls E), (nb095AlphaDummy434 f)),
        ((nb095AlphaDummy387 D R S_cls E), (nb095AlphaDummy390 f)),
        ((nb095AlphaDummy386 D R S_cls E), (nb095AlphaDummy389 f)),
        ((nb095AlphaDummy385 D R S_cls E), (nb095AlphaDummy388 f)),
        ((nb095AlphaDummy391 D R S_cls E), (nb095AlphaDummy392 f)),
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
        ((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)] (synC0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095AlphaDummy437 D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy444 D
        R S_cls E) ≠ (nb095AlphaDummy455 D R S_cls E) from (by
          unfold
            nb095AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy456 f) from (by
          unfold
            nb095AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠ (nb095AlphaDummy455
        D R S_cls E) from (by
          unfold
            nb095AlphaDummy455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy456 f) from (by
          unfold
            nb095AlphaDummy456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy444 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy447 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095AlphaDummy437
        D R S_cls E))).fv ∪ ((synC1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095AlphaDummy439 f))).fv ∪ ((synC1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy445 D
        R S_cls E) ≠ (nb095AlphaDummy457 D R S_cls E) from (by
          unfold
            nb095AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy458 f) from (by
          unfold
            nb095AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095AlphaDummy445 D
        R S_cls E) ≠ (nb095AlphaDummy457 D R S_cls E) from (by
          unfold
            nb095AlphaDummy457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy458 f) from (by
          unfold
            nb095AlphaDummy458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095AlphaDummy445 D R S_cls E) ≠
        (nb095AlphaDummy453 D R S_cls E) from (by
          unfold
            nb095AlphaDummy453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R S_cls
                    E)
                  0)))) (show (nb095AlphaDummy448 f) ≠ (nb095AlphaDummy454 f) from (by
          unfold
            nb095AlphaDummy454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy437 D R S_cls E) ≠
                                      (nb095AlphaDummy441 D R S_cls E) from (by
                                      unfold nb095AlphaDummy441;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from
                                    (by
                                      unfold nb095AlphaDummy442;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0441 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy441 D R S_cls E),
                                    (nb095AlphaDummy442 f)),
                                  ((nb095AlphaDummy437 D R S_cls E),
                                    (nb095AlphaDummy439 f)),
                                  ((nb095AlphaDummy438 D R S_cls E),
                                    (nb095AlphaDummy440 f)),
                                  ((nb095AlphaDummy463 D R S_cls E),
                                    (nb095AlphaDummy464 f)),
                                  ((nb095AlphaDummy461 D R S_cls E),
                                    (nb095AlphaDummy462 f)),
                                  ((nb095AlphaDummy430 D R S_cls E),
                                    (nb095AlphaDummy432 f)),
                                  ((nb095AlphaDummy429 D R S_cls E),
                                    (nb095AlphaDummy431 f)),
                                  ((nb095AlphaDummy459 D R S_cls E),
                                    (nb095AlphaDummy460 f)),
                                  ((nb095AlphaDummy433 D R S_cls E),
                                    (nb095AlphaDummy434 f)),
                                  ((nb095AlphaDummy387 D R S_cls E),
                                    (nb095AlphaDummy390 f)),
                                  ((nb095AlphaDummy386 D R S_cls E),
                                    (nb095AlphaDummy389 f)),
                                  ((nb095AlphaDummy385 D R S_cls E),
                                    (nb095AlphaDummy388 f)),
                                  ((nb095AlphaDummy391 D R S_cls E),
                                    (nb095AlphaDummy392 f)),
                                  ((nb095AlphaDummy383 D R S_cls E),
                                    (nb095AlphaDummy384 f)),
                                  ((nb095AlphaDummy381 D R S_cls E),
                                    (nb095AlphaDummy382 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095AlphaDummy437 D R S_cls E) ≠
                                    (nb095AlphaDummy441 D R S_cls E) from (by
                                    unfold nb095AlphaDummy441;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                  (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from (by
                                    unfold nb095AlphaDummy442;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0441 f)
                                            0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095AlphaDummy437 D R S_cls E) ≠
                                      (nb095AlphaDummy441 D R S_cls E) from (by
                                      unfold nb095AlphaDummy441;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                    (nb095AlphaDummy439 f) ≠ (nb095AlphaDummy442 f) from
                                    (by
                                      unfold nb095AlphaDummy442;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0441 f)
                                              0)))) (TAlphaVar.here _ _ _)))
                              (TAlphaClass.reflOfClosed [((nb095AlphaDummy441 D R S_cls E),
                                    (nb095AlphaDummy442 f)),
                                  ((nb095AlphaDummy437 D R S_cls E),
                                    (nb095AlphaDummy439 f)),
                                  ((nb095AlphaDummy438 D R S_cls E),
                                    (nb095AlphaDummy440 f)),
                                  ((nb095AlphaDummy463 D R S_cls E),
                                    (nb095AlphaDummy464 f)),
                                  ((nb095AlphaDummy461 D R S_cls E),
                                    (nb095AlphaDummy462 f)),
                                  ((nb095AlphaDummy430 D R S_cls E),
                                    (nb095AlphaDummy432 f)),
                                  ((nb095AlphaDummy429 D R S_cls E),
                                    (nb095AlphaDummy431 f)),
                                  ((nb095AlphaDummy459 D R S_cls E),
                                    (nb095AlphaDummy460 f)),
                                  ((nb095AlphaDummy433 D R S_cls E),
                                    (nb095AlphaDummy434 f)),
                                  ((nb095AlphaDummy387 D R S_cls E),
                                    (nb095AlphaDummy390 f)),
                                  ((nb095AlphaDummy386 D R S_cls E),
                                    (nb095AlphaDummy389 f)),
                                  ((nb095AlphaDummy385 D R S_cls E),
                                    (nb095AlphaDummy388 f)),
                                  ((nb095AlphaDummy391 D R S_cls E),
                                    (nb095AlphaDummy392 f)),
                                  ((nb095AlphaDummy383 D R S_cls E),
                                    (nb095AlphaDummy384 f)),
                                  ((nb095AlphaDummy381 D R S_cls E),
                                    (nb095AlphaDummy382 f)),
                                  ((nb095AlphaDummy001 D R S_cls E), u),
                                  ((nb095AlphaDummy002 D R S_cls E), x),
                                  ((nb095AlphaDummy000 D R S_cls E), f)]
                                (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0041`. -/
@[expose]
noncomputable def nb095SplitAlpha0041 (x : Var) (u : Var) (D : Class) (R : Class)
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
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
                                    ((nb095AlphaDummy383 D R S_cls E),
                                      (nb095AlphaDummy384 f)),
                                    ((nb095AlphaDummy381 D R S_cls E),
                                      (nb095AlphaDummy382 f)),
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
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
                                      ((nb095AlphaDummy383 D R S_cls E),
                                        (nb095AlphaDummy384 f)),
                                      ((nb095AlphaDummy381 D R S_cls E),
                                        (nb095AlphaDummy382 f)),
                                      ((nb095AlphaDummy001 D R S_cls E), u),
                                      ((nb095AlphaDummy002 D R S_cls E), x),
                                      ((nb095AlphaDummy000 D R S_cls E), f)] (synCnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb095_split_alpha_0042`. -/
@[expose]
noncomputable def nb095SplitAlpha0042 (x : Var) (u : Var) (D : Class) (R : Class)
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                            ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                            ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
        (nb095AlphaDummy392 f)), ((nb095AlphaDummy383 D R S_cls E),
        (nb095AlphaDummy384 f)), ((nb095AlphaDummy381 D R S_cls E),
        (nb095AlphaDummy382 f)), ((nb095AlphaDummy001 D R S_cls E), u),
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
        ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
        ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
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
                              ((nb095AlphaDummy383 D R S_cls E), (nb095AlphaDummy384 f)),
                              ((nb095AlphaDummy381 D R S_cls E), (nb095AlphaDummy382 f)),
                              ((nb095AlphaDummy001 D R S_cls E), u),
                              ((nb095AlphaDummy002 D R S_cls E), x),
                              ((nb095AlphaDummy000 D R S_cls E), f)]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
