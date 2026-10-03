/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part028Stage1


/-! NF weak partition development: NAR4H5C095M3Part028. -/


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
noncomputable def nb095_wpp_refl_0188 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TReflOn
      [((nb095_alpha_dummy_383 D R S_cls E), (nb095_alpha_dummy_384 f)),
        ((nb095_alpha_dummy_381 D R S_cls E), (nb095_alpha_dummy_382 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0192 x u D R S_cls f E)

@[expose]
noncomputable def nb095_split_alpha_0057 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_399 D R S_cls E), (nb095_alpha_dummy_400 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_399 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_399 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_393 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_394 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_385 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_393 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_394 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_400 f))
          (Class.cab (nb095_alpha_dummy_395 f)
            (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_400 f))
            (Class.cab (nb095_alpha_dummy_395 f)
              (syn_wrex (nb095_alpha_dummy_396 f) (Class.cv (nb095_alpha_dummy_388 f))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_395 f))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_396 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                      (nb095_alpha_dummy_394 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_394;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_396 f) from (by
                      unfold nb095_alpha_dummy_396;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0396 f) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                        (nb095_alpha_dummy_393 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_393;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 0))))
                    (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_395 f) from (by
                        unfold nb095_alpha_dummy_395;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0396 f) 0)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                          (nb095_alpha_dummy_399 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_399;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0398 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_400 f) from (by
                          unfold nb095_alpha_dummy_400;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0399 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                            (nb095_alpha_dummy_397 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_397;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0395 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_398 f) from (by
                            unfold nb095_alpha_dummy_398;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0397 f) 0))))
                        (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                  (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                              ((syn_ccnv (syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E))))).fv)
                            (by decide)) (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                              ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_394 D R S_cls E) ≠
                              (nb095_alpha_dummy_401 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_401;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0400 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_403 f) from (by
                              unfold nb095_alpha_dummy_403;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0401 f) 0))))
                          (TAlphaVar.there (show (nb095_alpha_dummy_394 D R S_cls E) ≠
                                (nb095_alpha_dummy_402 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_402;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0400 D R S_cls E) 1))))
                            (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_404 f) from (by
                                unfold nb095_alpha_dummy_404;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0401 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) (by decide))
                          (freshVar_injective (((Class.cv (nb095_alpha_dummy_396 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_408 D R S_cls E) from (by
          unfold nb095_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_411 f) from (by
          unfold nb095_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_407 D R S_cls E) from (by
          unfold nb095_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_410 f) from (by
          unfold nb095_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_405 D R S_cls E) from (by
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
                  (nb095_support_mem_0403 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_399 D R S_cls E), (nb095_alpha_dummy_400 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R S_cls
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
                    D R
                    S_cls E)
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R S_cls
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
                    D R
                    S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R S_cls
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
                    D R
                    S_cls E)
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R S_cls
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
                    D R
                    S_cls E)
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
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_399 D R S_cls E), (nb095_alpha_dummy_400 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R S_cls
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
                    D R
                    S_cls E)
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R S_cls
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
                    D R
                    S_cls E)
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_421 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R S_cls
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
                    D R
                    S_cls E)
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
                    D R S_cls
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
                    D R
                    S_cls E)
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
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_401 D R S_cls E) ≠
                                        (nb095_alpha_dummy_405 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from
                                      (by
                                        unfold nb095_alpha_dummy_406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_405 D R S_cls E),
                                      (nb095_alpha_dummy_406 f)),
                                    ((nb095_alpha_dummy_401 D R S_cls E),
                                      (nb095_alpha_dummy_403 f)),
                                    ((nb095_alpha_dummy_402 D R S_cls E),
                                      (nb095_alpha_dummy_404 f)),
                                    ((nb095_alpha_dummy_394 D R S_cls E),
                                      (nb095_alpha_dummy_396 f)),
                                    ((nb095_alpha_dummy_393 D R S_cls E),
                                      (nb095_alpha_dummy_395 f)),
                                    ((nb095_alpha_dummy_399 D R S_cls E),
                                      (nb095_alpha_dummy_400 f)),
                                    ((nb095_alpha_dummy_397 D R S_cls E),
                                      (nb095_alpha_dummy_398 f)),
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
                                    (nb095_alpha_dummy_401 D R S_cls E) ≠
                                      (nb095_alpha_dummy_405 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_405;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from
                                    (by
                                      unfold nb095_alpha_dummy_406;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb095_support_mem_0403 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_401 D R S_cls E) ≠
                                        (nb095_alpha_dummy_405 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from
                                      (by
                                        unfold nb095_alpha_dummy_406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_405 D R S_cls E),
                                      (nb095_alpha_dummy_406 f)),
                                    ((nb095_alpha_dummy_401 D R S_cls E),
                                      (nb095_alpha_dummy_403 f)),
                                    ((nb095_alpha_dummy_402 D R S_cls E),
                                      (nb095_alpha_dummy_404 f)),
                                    ((nb095_alpha_dummy_394 D R S_cls E),
                                      (nb095_alpha_dummy_396 f)),
                                    ((nb095_alpha_dummy_393 D R S_cls E),
                                      (nb095_alpha_dummy_395 f)),
                                    ((nb095_alpha_dummy_399 D R S_cls E),
                                      (nb095_alpha_dummy_400 f)),
                                    ((nb095_alpha_dummy_397 D R S_cls E),
                                      (nb095_alpha_dummy_398 f)),
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
                        (nb095_alpha_dummy_394 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_394;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E) 1))))
                    (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_396 f) from (by
                        unfold nb095_alpha_dummy_396;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0396 f) 1)))) (TAlphaVar.there
                      (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                          (nb095_alpha_dummy_393 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_393;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0394 D R S_cls E)
                                  0))))
                      (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_395 f) from (by
                          unfold nb095_alpha_dummy_395;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0396 f) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                            (nb095_alpha_dummy_399 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_399;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0398 D R S_cls E)
                                    0))))
                        (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_400 f) from (by
                            unfold nb095_alpha_dummy_400;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0399 f) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_385 D R S_cls E) ≠
                              (nb095_alpha_dummy_397 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_397;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0395 D R S_cls E)
                                      0))))
                          (show (nb095_alpha_dummy_388 f) ≠ (nb095_alpha_dummy_398 f) from (by
                              unfold nb095_alpha_dummy_398;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0397 f) 0))))
                          (TAlphaVar.there (freshVar_injective (((syn_ccnv
                                    (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv
                                        (nb095_alpha_dummy_000 D R S_cls E))))).fv) (by decide))
                            (freshVar_injective (((syn_ccnv (Class.cv f))).fv ∪
                                ((syn_ccnv (syn_ccnv (Class.cv f)))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_385 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_386 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_388 f))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_389 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_394 D R S_cls E) ≠
                                (nb095_alpha_dummy_401 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_401;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0400 D R S_cls E) 0))))
                            (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_403 f) from (by
                                unfold nb095_alpha_dummy_403;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0401 f) 0))))
                            (TAlphaVar.there (show (nb095_alpha_dummy_394 D R S_cls E) ≠
                                  (nb095_alpha_dummy_402 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_402;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0400 D R S_cls E) 1))))
                              (show (nb095_alpha_dummy_396 f) ≠ (nb095_alpha_dummy_404 f) from
                                (by
                                  unfold nb095_alpha_dummy_404;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0401 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_394 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_396 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_408 D R S_cls E) from (by
          unfold nb095_alpha_dummy_408;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_411 f) from (by
          unfold nb095_alpha_dummy_411;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f) 1)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_401 D R S_cls E) ≠ (nb095_alpha_dummy_407 D R S_cls E) from (by
          unfold nb095_alpha_dummy_407;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0404 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_410 f) from (by
          unfold nb095_alpha_dummy_410;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0405 f)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_401 D R S_cls E) ≠
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
                  (nb095_support_mem_0403 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_409 D R S_cls E), (nb095_alpha_dummy_412 f)),
        ((nb095_alpha_dummy_408 D R S_cls E), (nb095_alpha_dummy_411 f)),
        ((nb095_alpha_dummy_407 D R S_cls E), (nb095_alpha_dummy_410 f)),
        ((nb095_alpha_dummy_405 D R S_cls E), (nb095_alpha_dummy_406 f)),
        ((nb095_alpha_dummy_401 D R S_cls E), (nb095_alpha_dummy_403 f)),
        ((nb095_alpha_dummy_402 D R S_cls E), (nb095_alpha_dummy_404 f)),
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_399 D R S_cls E), (nb095_alpha_dummy_400 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_408
        D R S_cls E) ≠ (nb095_alpha_dummy_415 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R
                    S_cls E)
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
                    D R
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R
                    S_cls E)
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
                    D R
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
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0408
                    D R
                    S_cls E)
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
                    D R
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_409 D R S_cls E) ≠ (nb095_alpha_dummy_415
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_415;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0412
                    D R
                    S_cls E)
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
                    D R
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
        ((nb095_alpha_dummy_394 D R S_cls E), (nb095_alpha_dummy_396 f)),
        ((nb095_alpha_dummy_393 D R S_cls E), (nb095_alpha_dummy_395 f)),
        ((nb095_alpha_dummy_399 D R S_cls E), (nb095_alpha_dummy_400 f)),
        ((nb095_alpha_dummy_397 D R S_cls E), (nb095_alpha_dummy_398 f)),
        ((nb095_alpha_dummy_386 D R S_cls E), (nb095_alpha_dummy_389 f)),
        ((nb095_alpha_dummy_385 D R S_cls E), (nb095_alpha_dummy_388 f)),
        ((nb095_alpha_dummy_391 D R S_cls E), (nb095_alpha_dummy_392 f)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_401 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_401 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _))))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R
                    S_cls E)
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
                    D R
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_408 D R S_cls E) ≠ (nb095_alpha_dummy_419
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_419;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0416
                    D R
                    S_cls E)
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
                    D R
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
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_403 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_409
        D R S_cls E) ≠ (nb095_alpha_dummy_421 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_421;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0420
                    D R
                    S_cls E)
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
                    D R
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
                    D R
                    S_cls E)
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
                    D R
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
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_405;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0402 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_403 f) ≠
        (nb095_alpha_dummy_406 f) from (by
                                          unfold nb095_alpha_dummy_406;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0403 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_405 D R S_cls E),
                                        (nb095_alpha_dummy_406 f)),
                                      ((nb095_alpha_dummy_401 D R S_cls E),
                                        (nb095_alpha_dummy_403 f)),
                                      ((nb095_alpha_dummy_402 D R S_cls E),
                                        (nb095_alpha_dummy_404 f)),
                                      ((nb095_alpha_dummy_394 D R S_cls E),
                                        (nb095_alpha_dummy_396 f)),
                                      ((nb095_alpha_dummy_393 D R S_cls E),
                                        (nb095_alpha_dummy_395 f)),
                                      ((nb095_alpha_dummy_399 D R S_cls E),
                                        (nb095_alpha_dummy_400 f)),
                                      ((nb095_alpha_dummy_397 D R S_cls E),
                                        (nb095_alpha_dummy_398 f)),
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
                                      (nb095_alpha_dummy_401 D R S_cls E) ≠
                                        (nb095_alpha_dummy_405 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_405;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0402 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_403 f) ≠ (nb095_alpha_dummy_406 f) from
                                      (by
                                        unfold nb095_alpha_dummy_406;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb095_support_mem_0403 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_401 D R S_cls E) ≠
        (nb095_alpha_dummy_405 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_405;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0402 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_403 f) ≠
        (nb095_alpha_dummy_406 f) from (by
                                          unfold nb095_alpha_dummy_406;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0403 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_405 D R S_cls E),
                                        (nb095_alpha_dummy_406 f)),
                                      ((nb095_alpha_dummy_401 D R S_cls E),
                                        (nb095_alpha_dummy_403 f)),
                                      ((nb095_alpha_dummy_402 D R S_cls E),
                                        (nb095_alpha_dummy_404 f)),
                                      ((nb095_alpha_dummy_394 D R S_cls E),
                                        (nb095_alpha_dummy_396 f)),
                                      ((nb095_alpha_dummy_393 D R S_cls E),
                                        (nb095_alpha_dummy_395 f)),
                                      ((nb095_alpha_dummy_399 D R S_cls E),
                                        (nb095_alpha_dummy_400 f)),
                                      ((nb095_alpha_dummy_397 D R S_cls E),
                                        (nb095_alpha_dummy_398 f)),
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
