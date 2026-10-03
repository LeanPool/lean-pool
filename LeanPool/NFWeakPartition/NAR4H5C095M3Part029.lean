/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part028

/-! NF weak partition development: NAR4H5C095M3Part029. -/


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
noncomputable def nb095_split_alpha_0058 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_394 D R S_cls E))
          (Class.cv (nb095_alpha_dummy_386 D R S_cls E))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_396 f))
          (Class.cv (nb095_alpha_dummy_389 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
            (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))) (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there
          (show (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_394 D R S_cls E) from
            (by
              unfold nb095_alpha_dummy_394;
              with_reducible
                exact
                  (Nat.ne_of_lt
                    (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 1))))
          (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_396 f) from (by
              unfold nb095_alpha_dummy_396;
              with_reducible
                exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 1))))
          (TAlphaVar.there (show
              (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_393 D R S_cls E) from (by
                unfold nb095_alpha_dummy_393;
                with_reducible
                  exact
                    (Nat.ne_of_lt
                      (mem_lt_freshVar (nb095_support_mem_0422 D R S_cls E) 0))))
            (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_395 f) from (by
                unfold nb095_alpha_dummy_395;
                with_reducible
                  exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0424 f) 0))))
            (TAlphaVar.there (show
                (nb095_alpha_dummy_386 D R S_cls E) ≠ (nb095_alpha_dummy_423 D R S_cls E) from
                (by
                  unfold nb095_alpha_dummy_423;
                  with_reducible
                    exact
                      (Nat.ne_of_lt
                        (mem_lt_freshVar (nb095_support_mem_0426 D R S_cls E) 0))))
              (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_424 f) from (by
                  unfold nb095_alpha_dummy_424;
                  with_reducible
                    exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0427 f) 0))))
              (TAlphaVar.there (show (nb095_alpha_dummy_386 D R S_cls E) ≠
                    (nb095_alpha_dummy_397 D R S_cls E) from (by
                    unfold nb095_alpha_dummy_397;
                    with_reducible
                      exact
                        (Nat.ne_of_lt
                          (mem_lt_freshVar (nb095_support_mem_0423 D R S_cls E) 0))))
                (show (nb095_alpha_dummy_389 f) ≠ (nb095_alpha_dummy_398 f) from (by
                    unfold nb095_alpha_dummy_398;
                    with_reducible
                      exact
                        (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0425 f) 0))))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
                ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
                ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_394 D R S_cls E) ≠
                                        (nb095_alpha_dummy_401 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_401;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0400 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_403 f) from
                                      (by
                                        unfold nb095_alpha_dummy_403;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0401 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_394 D R S_cls E) ≠
        (nb095_alpha_dummy_402 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_402;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0400 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_396 f) ≠
        (nb095_alpha_dummy_404 f) from (by
                                          unfold nb095_alpha_dummy_404;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0401 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_394 D R S_cls E) ≠ (nb095_alpha_dummy_427 D R S_cls E) from (by
          unfold nb095_alpha_dummy_427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0430 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_428 f) from (by
          unfold nb095_alpha_dummy_428;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_394 D R S_cls E) ≠ (nb095_alpha_dummy_425 D R S_cls E) from (by
          unfold nb095_alpha_dummy_425;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0428 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_426 f) from (by
          unfold nb095_alpha_dummy_426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0429 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_394 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_396 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_408 D R S_cls E) from (by
          unfold nb095_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_411 f) from (by
          unfold nb095_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_407 D R S_cls E) from (by
          unfold nb095_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_410 f) from (by
          unfold nb095_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold
            nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_427 D R S_cls E), (nb095_alpha_dummy_428 f)),
        ((nb095_alpha_dummy_425 D R S_cls E), (nb095_alpha_dummy_426 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_415 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_427 D R S_cls E), (nb095_alpha_dummy_428 f)),
        ((nb095_alpha_dummy_425 D R S_cls E), (nb095_alpha_dummy_426 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_420 f) from (by
          unfold
            nb095_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408
        D R S_cls E) ≠ (nb095_alpha_dummy_419 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_420 f) from (by
          unfold
            nb095_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_421 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_422 f) from (by
          unfold
            nb095_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_421 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_422 f) from (by
          unfold
            nb095_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_405 D R S_cls E),
        (nb095_alpha_dummy_406 f)), ((nb095_alpha_dummy_401 D R S_cls E),
        (nb095_alpha_dummy_403 f)), ((nb095_alpha_dummy_402 D R S_cls E),
        (nb095_alpha_dummy_404 f)), ((nb095_alpha_dummy_427 D R S_cls E),
        (nb095_alpha_dummy_428 f)), ((nb095_alpha_dummy_425 D R S_cls E),
        (nb095_alpha_dummy_426 f)), ((nb095_alpha_dummy_394 D R S_cls E),
        (nb095_alpha_dummy_396 f)), ((nb095_alpha_dummy_393 D R S_cls E),
        (nb095_alpha_dummy_395 f)), ((nb095_alpha_dummy_423 D R S_cls E),
        (nb095_alpha_dummy_424 f)), ((nb095_alpha_dummy_397 D R S_cls E),
        (nb095_alpha_dummy_398 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_405 D R S_cls E),
        (nb095_alpha_dummy_406 f)), ((nb095_alpha_dummy_401 D R S_cls E),
        (nb095_alpha_dummy_403 f)), ((nb095_alpha_dummy_402 D R S_cls E),
        (nb095_alpha_dummy_404 f)), ((nb095_alpha_dummy_427 D R S_cls E),
        (nb095_alpha_dummy_428 f)), ((nb095_alpha_dummy_425 D R S_cls E),
        (nb095_alpha_dummy_426 f)), ((nb095_alpha_dummy_394 D R S_cls E),
        (nb095_alpha_dummy_396 f)), ((nb095_alpha_dummy_393 D R S_cls E),
        (nb095_alpha_dummy_395 f)), ((nb095_alpha_dummy_423 D R S_cls E),
        (nb095_alpha_dummy_424 f)), ((nb095_alpha_dummy_397 D R S_cls E),
        (nb095_alpha_dummy_398 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_394 D R S_cls E) ≠
                                        (nb095_alpha_dummy_401 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_401;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0400 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_403 f) from
                                      (by
                                        unfold nb095_alpha_dummy_403;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0401 f)
                                                0)))) (TAlphaVar.there (show
                                        (nb095_alpha_dummy_394 D R S_cls E) ≠
        (nb095_alpha_dummy_402 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_402;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0400 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_396 f) ≠
        (nb095_alpha_dummy_404 f) from (by
                                          unfold nb095_alpha_dummy_404;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0401 f) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_394 D R S_cls E) ≠ (nb095_alpha_dummy_427 D R S_cls E) from (by
          unfold nb095_alpha_dummy_427;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0430 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_428 f) from (by
          unfold nb095_alpha_dummy_428;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0431 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_394 D R S_cls E) ≠ (nb095_alpha_dummy_425 D R S_cls E) from (by
          unfold nb095_alpha_dummy_425;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0428 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_426 f) from (by
          unfold nb095_alpha_dummy_426;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0429 f) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_394 D R S_cls E))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb095_alpha_dummy_396 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_408 D R S_cls E) from (by
          unfold nb095_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404
                    D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_411 f) from (by
          unfold nb095_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405
                    f)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_407 D R S_cls E) from (by
          unfold nb095_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_410 f) from (by
          unfold nb095_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold
            nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_427 D R S_cls E), (nb095_alpha_dummy_428 f)),
        ((nb095_alpha_dummy_425 D R S_cls E), (nb095_alpha_dummy_426 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here
        _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_415 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0409
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0406
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0407
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_416 f) from (by
          unfold
            nb095_alpha_dummy_416;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0413
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_413 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_413;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0410
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_414 f) from (by
          unfold
            nb095_alpha_dummy_414;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0411
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_427 D R S_cls E), (nb095_alpha_dummy_428 f)),
        ((nb095_alpha_dummy_425 D R S_cls E), (nb095_alpha_dummy_426 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_420 f) from (by
          unfold
            nb095_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408
        D R S_cls E) ≠ (nb095_alpha_dummy_419 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_420 f) from (by
          unfold
            nb095_alpha_dummy_420;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0417
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0414
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_411 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0415
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_421 D R
        S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_422 f) from (by
          unfold
            nb095_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_421 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_422 f) from (by
          unfold
            nb095_alpha_dummy_422;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0421
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠
        (nb095_alpha_dummy_417 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_417;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0418
                    D
                    R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_412 f) ≠ (nb095_alpha_dummy_418 f) from (by
          unfold
            nb095_alpha_dummy_418;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0419
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_405 D R S_cls E),
        (nb095_alpha_dummy_406 f)), ((nb095_alpha_dummy_401 D R S_cls E),
        (nb095_alpha_dummy_403 f)), ((nb095_alpha_dummy_402 D R S_cls E),
        (nb095_alpha_dummy_404 f)), ((nb095_alpha_dummy_427 D R S_cls E),
        (nb095_alpha_dummy_428 f)), ((nb095_alpha_dummy_425 D R S_cls E),
        (nb095_alpha_dummy_426 f)), ((nb095_alpha_dummy_394 D R S_cls E),
        (nb095_alpha_dummy_396 f)), ((nb095_alpha_dummy_393 D R S_cls E),
        (nb095_alpha_dummy_395 f)), ((nb095_alpha_dummy_423 D R S_cls E),
        (nb095_alpha_dummy_424 f)), ((nb095_alpha_dummy_397 D R S_cls E),
        (nb095_alpha_dummy_398 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
        (show (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_405 D R S_cls E) from (by
          unfold nb095_alpha_dummy_405;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0402 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from (by
          unfold nb095_alpha_dummy_406;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0403 f) 0)))) (TAlphaVar.here _ _ _)))
        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_405 D R S_cls E),
        (nb095_alpha_dummy_406 f)), ((nb095_alpha_dummy_401 D R S_cls E),
        (nb095_alpha_dummy_403 f)), ((nb095_alpha_dummy_402 D R S_cls E),
        (nb095_alpha_dummy_404 f)), ((nb095_alpha_dummy_427 D R S_cls E),
        (nb095_alpha_dummy_428 f)), ((nb095_alpha_dummy_425 D R S_cls E),
        (nb095_alpha_dummy_426 f)), ((nb095_alpha_dummy_394 D R S_cls E),
        (nb095_alpha_dummy_396 f)), ((nb095_alpha_dummy_393 D R S_cls E),
        (nb095_alpha_dummy_395 f)), ((nb095_alpha_dummy_423 D R S_cls E),
        (nb095_alpha_dummy_424 f)), ((nb095_alpha_dummy_397 D R S_cls E),
        (nb095_alpha_dummy_398 f)), ((nb095_alpha_dummy_386 D R S_cls E),
        (nb095_alpha_dummy_389 f)), ((nb095_alpha_dummy_385 D R S_cls E),
        (nb095_alpha_dummy_388 f)), ((nb095_alpha_dummy_391 D R S_cls E),
        (nb095_alpha_dummy_392 f)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb095_alpha_dummy_425 D R S_cls E), (nb095_alpha_dummy_426 f)),
                    ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
                    ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
                    ((nb095_alpha_dummy_423 D R S_cls E), (nb095_alpha_dummy_424 f)),
                    ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
                    ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
                    ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
                    ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                    ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

@[expose]
noncomputable def nb095_split_alpha_0059 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_435 D R S_cls E), (nb095_alpha_dummy_436 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_435 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_435 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_429 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_430 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_429 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_436 f))
          (Class.cab (nb095_alpha_dummy_431 f)
            (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_436 f))
            (Class.cab (nb095_alpha_dummy_431 f)
              (syn_wrex (nb095_alpha_dummy_432 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_431 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_432 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                      (nb095_alpha_dummy_430 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_430;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_432 f) from (by
                      unfold nb095_alpha_dummy_432;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0434 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                        (nb095_alpha_dummy_429 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_429;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_431 f) from (by
                        unfold nb095_alpha_dummy_431;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0434 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                          (nb095_alpha_dummy_435 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_435;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0436 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_436 f) from (by
                          unfold nb095_alpha_dummy_436;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0437 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                            (nb095_alpha_dummy_433 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_433;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0433 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_434 f) from (by
                            unfold nb095_alpha_dummy_434;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0435 f) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                  (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                              ((syn_ccnv (syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv
                                        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_390 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                              (nb095_alpha_dummy_437 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_437;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0438 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_439 f) from (by
                              unfold nb095_alpha_dummy_439;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                (nb095_alpha_dummy_438 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_438;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0438 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_440 f) from (by
                                unfold nb095_alpha_dummy_440;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_432 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_444 D R S_cls E) from (by
          unfold nb095_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_447 f) from (by
          unfold nb095_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_443 D R S_cls E) from (by
          unfold nb095_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_446 f) from (by
          unfold nb095_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_441 D R S_cls E) from (by
          unfold nb095_alpha_dummy_441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from (by
          unfold nb095_alpha_dummy_442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_435 D R S_cls E), (nb095_alpha_dummy_436 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_444
        D R S_cls E) ≠ (nb095_alpha_dummy_451 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_435 D R S_cls E), (nb095_alpha_dummy_436 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_437 D R S_cls E) ≠
                                        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_441;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                      (by
                                        unfold nb095_alpha_dummy_442;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0441 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_441 D R S_cls E),
                                      (nb095_alpha_dummy_442 f)),
                                    ((nb095_alpha_dummy_437 D R S_cls E),
                                      (nb095_alpha_dummy_439 f)),
                                    ((nb095_alpha_dummy_438 D R S_cls E),
                                      (nb095_alpha_dummy_440 f)),
                                    ((nb095_alpha_dummy_430 D R S_cls E),
                                      (nb095_alpha_dummy_432 f)),
                                    ((nb095_alpha_dummy_429 D R S_cls E),
                                      (nb095_alpha_dummy_431 f)),
                                    ((nb095_alpha_dummy_435 D R S_cls E),
                                      (nb095_alpha_dummy_436 f)),
                                    ((nb095_alpha_dummy_433 D R S_cls E),
                                      (nb095_alpha_dummy_434 f)),
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
                                    (nb095_alpha_dummy_437 D R S_cls E) ≠
                                      (nb095_alpha_dummy_441 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_441;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                    (by
                                      unfold nb095_alpha_dummy_442;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0441 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_437 D R S_cls E) ≠
                                        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_441;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                      (by
                                        unfold nb095_alpha_dummy_442;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0441 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_441 D R S_cls E),
                                      (nb095_alpha_dummy_442 f)),
                                    ((nb095_alpha_dummy_437 D R S_cls E),
                                      (nb095_alpha_dummy_439 f)),
                                    ((nb095_alpha_dummy_438 D R S_cls E),
                                      (nb095_alpha_dummy_440 f)),
                                    ((nb095_alpha_dummy_430 D R S_cls E),
                                      (nb095_alpha_dummy_432 f)),
                                    ((nb095_alpha_dummy_429 D R S_cls E),
                                      (nb095_alpha_dummy_431 f)),
                                    ((nb095_alpha_dummy_435 D R S_cls E),
                                      (nb095_alpha_dummy_436 f)),
                                    ((nb095_alpha_dummy_433 D R S_cls E),
                                      (nb095_alpha_dummy_434 f)),
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
                  (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                        (nb095_alpha_dummy_430 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_430;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_432 f) from (by
                        unfold nb095_alpha_dummy_432;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0434 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                          (nb095_alpha_dummy_429 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_429;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0432 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_431 f) from (by
                          unfold nb095_alpha_dummy_431;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0434 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                            (nb095_alpha_dummy_435 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_435;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0436 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_436 f) from (by
                            unfold nb095_alpha_dummy_436;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0437 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                              (nb095_alpha_dummy_433 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_433;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0433 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_434 f) from (by
                              unfold nb095_alpha_dummy_434;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0435 f) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv
                                        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.there (freshVar_injective (((syn_ccnv (Class.cv
                                        (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_ccnv
                                      (syn_ccnv (Class.cv
        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide)) (freshVar_injective
                                (((syn_ccnv (Class.cv f))).fv ∪
                                  ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_387 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_390 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_430 D R S_cls E) ≠
                                (nb095_alpha_dummy_437 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_437;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0438 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_439 f) from (by
                                unfold nb095_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                  (nb095_alpha_dummy_438 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0438 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_440 f) from
                                (by
                                  unfold nb095_alpha_dummy_440;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_432 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_444 D R S_cls E) from (by
          unfold nb095_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_447 f) from (by
          unfold nb095_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_443 D R S_cls E) from (by
          unfold nb095_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_446 f) from (by
          unfold nb095_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
          unfold nb095_alpha_dummy_441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from (by
          unfold nb095_alpha_dummy_442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_435 D R S_cls E), (nb095_alpha_dummy_436 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_444
        D R S_cls E) ≠ (nb095_alpha_dummy_451 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_435 D R S_cls E), (nb095_alpha_dummy_436 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_435 D R S_cls E),
                                        (nb095_alpha_dummy_436 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
                                      (nb095_alpha_dummy_437 D R S_cls E) ≠
                                        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_441;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                      (by
                                        unfold nb095_alpha_dummy_442;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0441 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_435 D R S_cls E),
                                        (nb095_alpha_dummy_436 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
noncomputable def nb095_split_alpha_0060 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_461 D R S_cls E))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_430 D R S_cls E)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_461 D R S_cls E))
            (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.neg (syn_wa (Wff.classMem (Class.cv (nb095_alpha_dummy_462 f))
            (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_432 f)))))
          (Wff.classMem (Class.cv (nb095_alpha_dummy_462 f))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_430 D R S_cls E) ≠
                                (nb095_alpha_dummy_437 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_437;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0438 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_439 f) from (by
                                unfold nb095_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                  (nb095_alpha_dummy_438 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0438 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_440 f) from
                                (by
                                  unfold nb095_alpha_dummy_440;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                    (nb095_alpha_dummy_463 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_463;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0468 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_464 f) from (by
                                    unfold nb095_alpha_dummy_464;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0469 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_430 D R S_cls E) ≠
                                      (nb095_alpha_dummy_461 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_461;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0466 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_462 f) from
                                    (by
                                      unfold nb095_alpha_dummy_462;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0467 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_432 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_444 D R S_cls E) from (by
          unfold nb095_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_447 f) from (by
          unfold nb095_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_443 D R S_cls E) from (by
          unfold nb095_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_446 f) from (by
          unfold nb095_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
          unfold nb095_alpha_dummy_441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from (by
          unfold nb095_alpha_dummy_442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_463 D R S_cls E), (nb095_alpha_dummy_464 f)),
        ((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_444
        D R S_cls E) ≠ (nb095_alpha_dummy_451 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_463 D R S_cls E), (nb095_alpha_dummy_464 f)),
        ((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_463 D R S_cls E),
                                        (nb095_alpha_dummy_464 f)),
                                      ((nb095_alpha_dummy_461 D R S_cls E),
                                        (nb095_alpha_dummy_462 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_459 D R S_cls E),
                                        (nb095_alpha_dummy_460 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
                                      (nb095_alpha_dummy_437 D R S_cls E) ≠
                                        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_441;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                      (by
                                        unfold nb095_alpha_dummy_442;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0441 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_463 D R S_cls E),
                                        (nb095_alpha_dummy_464 f)),
                                      ((nb095_alpha_dummy_461 D R S_cls E),
                                        (nb095_alpha_dummy_462 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_459 D R S_cls E),
                                        (nb095_alpha_dummy_460 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
                              (nb095_alpha_dummy_430 D R S_cls E) ≠
                                (nb095_alpha_dummy_437 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_437;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0438 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_439 f) from (by
                                unfold nb095_alpha_dummy_439;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0439 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                  (nb095_alpha_dummy_438 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_438;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0438 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_440 f) from
                                (by
                                  unfold nb095_alpha_dummy_440;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0439 f) 1))))
                              (TAlphaVar.there (show (nb095_alpha_dummy_430 D R S_cls E) ≠
                                    (nb095_alpha_dummy_463 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_463;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0468 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_464 f) from (by
                                    unfold nb095_alpha_dummy_464;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb095_support_mem_0469 f)
                                            0)))) (TAlphaVar.there (show
                                    (nb095_alpha_dummy_430 D R S_cls E) ≠
                                      (nb095_alpha_dummy_461 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_461;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0466 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_432 f) ≠ (nb095_alpha_dummy_462 f) from
                                    (by
                                      unfold nb095_alpha_dummy_462;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0467 f)
                                              0)))) (TAlphaVar.here _ _ _)))))))
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_430 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_432 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_444 D R S_cls E) from (by
          unfold nb095_alpha_dummy_444;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_447 f) from (by
          unfold nb095_alpha_dummy_447;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_437 D R S_cls E) ≠ (nb095_alpha_dummy_443 D R S_cls E) from (by
          unfold nb095_alpha_dummy_443;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0442 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_446 f) from (by
          unfold nb095_alpha_dummy_446;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0443 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
          unfold nb095_alpha_dummy_441;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0440 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from (by
          unfold nb095_alpha_dummy_442;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0441 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_463 D R S_cls E), (nb095_alpha_dummy_464 f)),
        ((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_444
        D R S_cls E) ≠ (nb095_alpha_dummy_451 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0446
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0447
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0444
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0445
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠ (nb095_alpha_dummy_451
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_451;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0450
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_452 f) from (by
          unfold
            nb095_alpha_dummy_452;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0451
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_449 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_449;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0448
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_450 f) from (by
          unfold
            nb095_alpha_dummy_450;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0449
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_445 D R S_cls E), (nb095_alpha_dummy_448 f)),
        ((nb095_alpha_dummy_444 D R S_cls E), (nb095_alpha_dummy_447 f)),
        ((nb095_alpha_dummy_443 D R S_cls E), (nb095_alpha_dummy_446 f)),
        ((nb095_alpha_dummy_441 D R S_cls E), (nb095_alpha_dummy_442 f)),
        ((nb095_alpha_dummy_437 D R S_cls E), (nb095_alpha_dummy_439 f)),
        ((nb095_alpha_dummy_438 D R S_cls E), (nb095_alpha_dummy_440 f)),
        ((nb095_alpha_dummy_463 D R S_cls E), (nb095_alpha_dummy_464 f)),
        ((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
        ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
        ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
        ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
        ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
        ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_437 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠ (nb095_alpha_dummy_455
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_455;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0454
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_456 f) from (by
          unfold
            nb095_alpha_dummy_456;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0455
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_444 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0452
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_447 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0453
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_437
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_439 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_445
        D R S_cls E) ≠ (nb095_alpha_dummy_457 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_457;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0458
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_458 f) from (by
          unfold
            nb095_alpha_dummy_458;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0459
                    f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_445 D R S_cls E) ≠
        (nb095_alpha_dummy_453 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_453;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0456
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_448 f) ≠ (nb095_alpha_dummy_454 f) from (by
          unfold
            nb095_alpha_dummy_454;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0457
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_463 D R S_cls E),
                                        (nb095_alpha_dummy_464 f)),
                                      ((nb095_alpha_dummy_461 D R S_cls E),
                                        (nb095_alpha_dummy_462 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_459 D R S_cls E),
                                        (nb095_alpha_dummy_460 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
                                      (nb095_alpha_dummy_437 D R S_cls E) ≠
                                        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_441;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0440 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_439 f) ≠ (nb095_alpha_dummy_442 f) from
                                      (by
                                        unfold nb095_alpha_dummy_442;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0441 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_437 D R S_cls E) ≠
        (nb095_alpha_dummy_441 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_441;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0440 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_439 f) ≠
        (nb095_alpha_dummy_442 f) from (by
                                          unfold nb095_alpha_dummy_442;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0441 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_441 D R S_cls E),
                                        (nb095_alpha_dummy_442 f)),
                                      ((nb095_alpha_dummy_437 D R S_cls E),
                                        (nb095_alpha_dummy_439 f)),
                                      ((nb095_alpha_dummy_438 D R S_cls E),
                                        (nb095_alpha_dummy_440 f)),
                                      ((nb095_alpha_dummy_463 D R S_cls E),
                                        (nb095_alpha_dummy_464 f)),
                                      ((nb095_alpha_dummy_461 D R S_cls E),
                                        (nb095_alpha_dummy_462 f)),
                                      ((nb095_alpha_dummy_430 D R S_cls E),
                                        (nb095_alpha_dummy_432 f)),
                                      ((nb095_alpha_dummy_429 D R S_cls E),
                                        (nb095_alpha_dummy_431 f)),
                                      ((nb095_alpha_dummy_459 D R S_cls E),
                                        (nb095_alpha_dummy_460 f)),
                                      ((nb095_alpha_dummy_433 D R S_cls E),
                                        (nb095_alpha_dummy_434 f)),
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
          [((nb095_alpha_dummy_461 D R S_cls E), (nb095_alpha_dummy_462 f)),
            ((nb095_alpha_dummy_430 D R S_cls E), (nb095_alpha_dummy_432 f)),
            ((nb095_alpha_dummy_429 D R S_cls E), (nb095_alpha_dummy_431 f)),
            ((nb095_alpha_dummy_459 D R S_cls E), (nb095_alpha_dummy_460 f)),
            ((nb095_alpha_dummy_433 D R S_cls E), (nb095_alpha_dummy_434 f)),
            ((nb095_alpha_dummy_387 D R S_cls E), (nb095_alpha_dummy_390 f)),
            ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
            ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
            ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
            ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
            ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
