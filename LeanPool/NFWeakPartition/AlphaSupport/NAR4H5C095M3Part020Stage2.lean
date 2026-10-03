/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part020Stage1


/-! NF weak partition development: NAR4H5C095M3Part020. -/


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
noncomputable def nb095_split_alpha_0032 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_351 D R S_cls E))
          (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_351 D R S_cls E))
            (Class.cab (nb095_alpha_dummy_345 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_346 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_340 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_345 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_352 u S_cls))
          (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
              (Class.cv (nb095_alpha_dummy_342 u S_cls))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_352 u S_cls))
            (Class.cab (nb095_alpha_dummy_347 u S_cls) (syn_wrex (nb095_alpha_dummy_348 u S_cls)
                (Class.cv (nb095_alpha_dummy_342 u S_cls))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_347 u S_cls))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                      (nb095_alpha_dummy_346 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_346;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1))))
                  (show (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from
                    (by
                      unfold nb095_alpha_dummy_348;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
                  (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                        (nb095_alpha_dummy_345 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_345;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from (by
                        unfold nb095_alpha_dummy_347;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                          (nb095_alpha_dummy_351 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_351;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0356 D R S_cls E)
                                  0)))) (show
                        (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_352 u S_cls) from
                        (by
                          unfold nb095_alpha_dummy_352;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0357 u S_cls) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                            (nb095_alpha_dummy_349 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_349;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0353 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_342 u S_cls) ≠
                            (nb095_alpha_dummy_350 u S_cls) from (by
                            unfold nb095_alpha_dummy_350;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0355 u S_cls) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
                      ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                              (nb095_alpha_dummy_353 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_353;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                              (nb095_alpha_dummy_355 u S_cls) from (by
                              unfold nb095_alpha_dummy_355;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      0)))) (TAlphaVar.there (show
                              (nb095_alpha_dummy_346 D R S_cls E) ≠
                                (nb095_alpha_dummy_354 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_354;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0358 D R S_cls E) 1)))) (show
                              (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_356 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_356;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                        1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_360 D R S_cls E) from (by
          unfold nb095_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  1)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_363 u S_cls)
        from (by
          unfold nb095_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_359 D R S_cls E) from (by
          unfold nb095_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_362 u S_cls)
        from (by
          unfold nb095_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360
        D R S_cls E) ≠ (nb095_alpha_dummy_367 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360
        D R S_cls E) ≠ (nb095_alpha_dummy_371 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361
        D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361
        D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_353 D R S_cls E) ≠
                                        (nb095_alpha_dummy_357 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_355 u S_cls) ≠
                                        (nb095_alpha_dummy_358 u S_cls) from (by
                                        unfold nb095_alpha_dummy_358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_357 D R S_cls E),
                                      (nb095_alpha_dummy_358 u S_cls)),
                                    ((nb095_alpha_dummy_353 D R S_cls E),
                                      (nb095_alpha_dummy_355 u S_cls)),
                                    ((nb095_alpha_dummy_354 D R S_cls E),
                                      (nb095_alpha_dummy_356 u S_cls)),
                                    ((nb095_alpha_dummy_346 D R S_cls E),
                                      (nb095_alpha_dummy_348 u S_cls)),
                                    ((nb095_alpha_dummy_345 D R S_cls E),
                                      (nb095_alpha_dummy_347 u S_cls)),
                                    ((nb095_alpha_dummy_351 D R S_cls E),
                                      (nb095_alpha_dummy_352 u S_cls)),
                                    ((nb095_alpha_dummy_349 D R S_cls E),
                                      (nb095_alpha_dummy_350 u S_cls)),
                                    ((nb095_alpha_dummy_340 D R S_cls E),
                                      (nb095_alpha_dummy_342 u S_cls)),
                                    ((nb095_alpha_dummy_339 D R S_cls E),
                                      (nb095_alpha_dummy_341 u S_cls)),
                                    ((nb095_alpha_dummy_337 D R S_cls E),
                                      (nb095_alpha_dummy_338 u S_cls E)),
                                    ((nb095_alpha_dummy_335 D R S_cls E),
                                      (nb095_alpha_dummy_336 u S_cls E)),
                                    ((nb095_alpha_dummy_293 D R S_cls E),
                                      (nb095_alpha_dummy_294 u S_cls f E)),
                                    ((nb095_alpha_dummy_291 D R S_cls E),
                                      (nb095_alpha_dummy_292 u S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_353 D R S_cls E) ≠
                                      (nb095_alpha_dummy_357 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_355 u S_cls) ≠
                                      (nb095_alpha_dummy_358 u S_cls) from (by
                                      unfold nb095_alpha_dummy_358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_353 D R S_cls E) ≠
                                        (nb095_alpha_dummy_357 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_355 u S_cls) ≠
                                        (nb095_alpha_dummy_358 u S_cls) from (by
                                        unfold nb095_alpha_dummy_358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb095_alpha_dummy_357 D R S_cls E),
                                      (nb095_alpha_dummy_358 u S_cls)),
                                    ((nb095_alpha_dummy_353 D R S_cls E),
                                      (nb095_alpha_dummy_355 u S_cls)),
                                    ((nb095_alpha_dummy_354 D R S_cls E),
                                      (nb095_alpha_dummy_356 u S_cls)),
                                    ((nb095_alpha_dummy_346 D R S_cls E),
                                      (nb095_alpha_dummy_348 u S_cls)),
                                    ((nb095_alpha_dummy_345 D R S_cls E),
                                      (nb095_alpha_dummy_347 u S_cls)),
                                    ((nb095_alpha_dummy_351 D R S_cls E),
                                      (nb095_alpha_dummy_352 u S_cls)),
                                    ((nb095_alpha_dummy_349 D R S_cls E),
                                      (nb095_alpha_dummy_350 u S_cls)),
                                    ((nb095_alpha_dummy_340 D R S_cls E),
                                      (nb095_alpha_dummy_342 u S_cls)),
                                    ((nb095_alpha_dummy_339 D R S_cls E),
                                      (nb095_alpha_dummy_341 u S_cls)),
                                    ((nb095_alpha_dummy_337 D R S_cls E),
                                      (nb095_alpha_dummy_338 u S_cls E)),
                                    ((nb095_alpha_dummy_335 D R S_cls E),
                                      (nb095_alpha_dummy_336 u S_cls E)),
                                    ((nb095_alpha_dummy_293 D R S_cls E),
                                      (nb095_alpha_dummy_294 u S_cls f E)),
                                    ((nb095_alpha_dummy_291 D R S_cls E),
                                      (nb095_alpha_dummy_292 u S_cls f E)),
                                    ((nb095_alpha_dummy_001 D R S_cls E), u),
                                    ((nb095_alpha_dummy_002 D R S_cls E), x),
                                    ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                        (nb095_alpha_dummy_346 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_346;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_348 u S_cls) from (by
                        unfold nb095_alpha_dummy_348;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                          (nb095_alpha_dummy_345 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_345;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0352 D R S_cls E)
                                  0)))) (show
                        (nb095_alpha_dummy_342 u S_cls) ≠ (nb095_alpha_dummy_347 u S_cls) from
                        (by
                          unfold nb095_alpha_dummy_347;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0354 u S_cls) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                            (nb095_alpha_dummy_351 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_351;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0356 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_342 u S_cls) ≠
                            (nb095_alpha_dummy_352 u S_cls) from (by
                            unfold nb095_alpha_dummy_352;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0357 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_340 D R S_cls E) ≠
                              (nb095_alpha_dummy_349 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_349;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0353 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_342 u S_cls) ≠
                              (nb095_alpha_dummy_350 u S_cls) from (by
                              unfold nb095_alpha_dummy_350;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0355 u S_cls)
                                      0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_340 D R S_cls E))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_339 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_342 u S_cls))).fv ∪
                        ((Class.cv (nb095_alpha_dummy_341 u S_cls))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_346 D R S_cls E) ≠
                                (nb095_alpha_dummy_353 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_353;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0358 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_355 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_355;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095_alpha_dummy_346 D R S_cls E) ≠
                                  (nb095_alpha_dummy_354 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_354;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0358 D R S_cls E) 1)))) (show
                                (nb095_alpha_dummy_348 u S_cls) ≠
                                  (nb095_alpha_dummy_356 u S_cls) from (by
                                  unfold nb095_alpha_dummy_356;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_360 D R S_cls E) from (by
          unfold nb095_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  1)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_363 u S_cls)
        from (by
          unfold nb095_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_359 D R S_cls E) from (by
          unfold nb095_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_362 u S_cls)
        from (by
          unfold nb095_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u
                    S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360
        D R S_cls E) ≠ (nb095_alpha_dummy_367 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353 D R
        S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360
        D R S_cls E) ≠ (nb095_alpha_dummy_371 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u
                    S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361
        D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361
        D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R
                    S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u
                    S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_357;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0360 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠
        (nb095_alpha_dummy_358 u S_cls) from (by
                                          unfold nb095_alpha_dummy_358;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0361 u S_cls) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_357 D R S_cls E),
                                        (nb095_alpha_dummy_358 u S_cls)),
                                      ((nb095_alpha_dummy_353 D R S_cls E),
                                        (nb095_alpha_dummy_355 u S_cls)),
                                      ((nb095_alpha_dummy_354 D R S_cls E),
                                        (nb095_alpha_dummy_356 u S_cls)),
                                      ((nb095_alpha_dummy_346 D R S_cls E),
                                        (nb095_alpha_dummy_348 u S_cls)),
                                      ((nb095_alpha_dummy_345 D R S_cls E),
                                        (nb095_alpha_dummy_347 u S_cls)),
                                      ((nb095_alpha_dummy_351 D R S_cls E),
                                        (nb095_alpha_dummy_352 u S_cls)),
                                      ((nb095_alpha_dummy_349 D R S_cls E),
                                        (nb095_alpha_dummy_350 u S_cls)),
                                      ((nb095_alpha_dummy_340 D R S_cls E),
                                        (nb095_alpha_dummy_342 u S_cls)),
                                      ((nb095_alpha_dummy_339 D R S_cls E),
                                        (nb095_alpha_dummy_341 u S_cls)),
                                      ((nb095_alpha_dummy_337 D R S_cls E),
                                        (nb095_alpha_dummy_338 u S_cls E)),
                                      ((nb095_alpha_dummy_335 D R S_cls E),
                                        (nb095_alpha_dummy_336 u S_cls E)),
                                      ((nb095_alpha_dummy_293 D R S_cls E),
                                        (nb095_alpha_dummy_294 u S_cls f E)),
                                      ((nb095_alpha_dummy_291 D R S_cls E),
                                        (nb095_alpha_dummy_292 u S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_353 D R S_cls E) ≠
                                        (nb095_alpha_dummy_357 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_357;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                      (nb095_alpha_dummy_355 u S_cls) ≠
                                        (nb095_alpha_dummy_358 u S_cls) from (by
                                        unfold nb095_alpha_dummy_358;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0361 u S_cls) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_357;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0360 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠
        (nb095_alpha_dummy_358 u S_cls) from (by
                                          unfold nb095_alpha_dummy_358;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0361 u S_cls) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb095_alpha_dummy_357 D R S_cls E),
                                        (nb095_alpha_dummy_358 u S_cls)),
                                      ((nb095_alpha_dummy_353 D R S_cls E),
                                        (nb095_alpha_dummy_355 u S_cls)),
                                      ((nb095_alpha_dummy_354 D R S_cls E),
                                        (nb095_alpha_dummy_356 u S_cls)),
                                      ((nb095_alpha_dummy_346 D R S_cls E),
                                        (nb095_alpha_dummy_348 u S_cls)),
                                      ((nb095_alpha_dummy_345 D R S_cls E),
                                        (nb095_alpha_dummy_347 u S_cls)),
                                      ((nb095_alpha_dummy_351 D R S_cls E),
                                        (nb095_alpha_dummy_352 u S_cls)),
                                      ((nb095_alpha_dummy_349 D R S_cls E),
                                        (nb095_alpha_dummy_350 u S_cls)),
                                      ((nb095_alpha_dummy_340 D R S_cls E),
                                        (nb095_alpha_dummy_342 u S_cls)),
                                      ((nb095_alpha_dummy_339 D R S_cls E),
                                        (nb095_alpha_dummy_341 u S_cls)),
                                      ((nb095_alpha_dummy_337 D R S_cls E),
                                        (nb095_alpha_dummy_338 u S_cls E)),
                                      ((nb095_alpha_dummy_335 D R S_cls E),
                                        (nb095_alpha_dummy_336 u S_cls E)),
                                      ((nb095_alpha_dummy_293 D R S_cls E),
                                        (nb095_alpha_dummy_294 u S_cls f E)),
                                      ((nb095_alpha_dummy_291 D R S_cls E),
                                        (nb095_alpha_dummy_292 u S_cls f E)),
                                      ((nb095_alpha_dummy_001 D R S_cls E), u),
                                      ((nb095_alpha_dummy_002 D R S_cls E), x),
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb095_split_alpha_0033 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.classMem (Class.cv (nb095_alpha_dummy_377 D R S_cls E))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_378 u S_cls))
        (syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls))))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                            (nb095_alpha_dummy_353 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_353;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                            (nb095_alpha_dummy_355 u S_cls) from (by
                            unfold nb095_alpha_dummy_355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                              (nb095_alpha_dummy_354 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_354;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      1)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                              (nb095_alpha_dummy_356 u S_cls) from (by
                              unfold nb095_alpha_dummy_356;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      1)))) (TAlphaVar.there (show
                              (nb095_alpha_dummy_346 D R S_cls E) ≠
                                (nb095_alpha_dummy_379 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_379;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0388 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_380 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_380;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0389 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095_alpha_dummy_346 D R S_cls E) ≠
                                  (nb095_alpha_dummy_377 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_377;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0386 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_348 u S_cls) ≠
                                  (nb095_alpha_dummy_378 u S_cls) from (by
                                  unfold nb095_alpha_dummy_378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0387 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                        (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_360 D R S_cls E) from (by
          unfold nb095_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_363 u S_cls)
        from (by
          unfold nb095_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_359 D R S_cls E) from (by
          unfold nb095_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_362 u S_cls)
        from (by
          unfold nb095_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_379 D R S_cls E), (nb095_alpha_dummy_380 u S_cls)),
        ((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_379 D R S_cls E), (nb095_alpha_dummy_380 u S_cls)),
        ((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360 D
        R S_cls E) ≠ (nb095_alpha_dummy_371 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D
        R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D
        R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_353 D R S_cls E) ≠
                                      (nb095_alpha_dummy_357 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_355 u S_cls) ≠
                                      (nb095_alpha_dummy_358 u S_cls) from (by
                                      unfold nb095_alpha_dummy_358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                [((nb095_alpha_dummy_357 D R S_cls E),
                                    (nb095_alpha_dummy_358 u S_cls)),
                                  ((nb095_alpha_dummy_353 D R S_cls E),
                                    (nb095_alpha_dummy_355 u S_cls)),
                                  ((nb095_alpha_dummy_354 D R S_cls E),
                                    (nb095_alpha_dummy_356 u S_cls)),
                                  ((nb095_alpha_dummy_379 D R S_cls E),
                                    (nb095_alpha_dummy_380 u S_cls)),
                                  ((nb095_alpha_dummy_377 D R S_cls E),
                                    (nb095_alpha_dummy_378 u S_cls)),
                                  ((nb095_alpha_dummy_346 D R S_cls E),
                                    (nb095_alpha_dummy_348 u S_cls)),
                                  ((nb095_alpha_dummy_345 D R S_cls E),
                                    (nb095_alpha_dummy_347 u S_cls)),
                                  ((nb095_alpha_dummy_375 D R S_cls E),
                                    (nb095_alpha_dummy_376 u S_cls)),
                                  ((nb095_alpha_dummy_349 D R S_cls E),
                                    (nb095_alpha_dummy_350 u S_cls)),
                                  ((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_293 D R S_cls E),
                                    (nb095_alpha_dummy_294 u S_cls f E)),
                                  ((nb095_alpha_dummy_291 D R S_cls E),
                                    (nb095_alpha_dummy_292 u S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_353 D R S_cls E) ≠
                                    (nb095_alpha_dummy_357 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_357;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_355 u S_cls) ≠
                                    (nb095_alpha_dummy_358 u S_cls) from (by
                                    unfold nb095_alpha_dummy_358;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0361 u S_cls) 0))))
                                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_353 D R S_cls E) ≠
                                      (nb095_alpha_dummy_357 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_355 u S_cls) ≠
                                      (nb095_alpha_dummy_358 u S_cls) from (by
                                      unfold nb095_alpha_dummy_358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                [((nb095_alpha_dummy_357 D R S_cls E),
                                    (nb095_alpha_dummy_358 u S_cls)),
                                  ((nb095_alpha_dummy_353 D R S_cls E),
                                    (nb095_alpha_dummy_355 u S_cls)),
                                  ((nb095_alpha_dummy_354 D R S_cls E),
                                    (nb095_alpha_dummy_356 u S_cls)),
                                  ((nb095_alpha_dummy_379 D R S_cls E),
                                    (nb095_alpha_dummy_380 u S_cls)),
                                  ((nb095_alpha_dummy_377 D R S_cls E),
                                    (nb095_alpha_dummy_378 u S_cls)),
                                  ((nb095_alpha_dummy_346 D R S_cls E),
                                    (nb095_alpha_dummy_348 u S_cls)),
                                  ((nb095_alpha_dummy_345 D R S_cls E),
                                    (nb095_alpha_dummy_347 u S_cls)),
                                  ((nb095_alpha_dummy_375 D R S_cls E),
                                    (nb095_alpha_dummy_376 u S_cls)),
                                  ((nb095_alpha_dummy_349 D R S_cls E),
                                    (nb095_alpha_dummy_350 u S_cls)),
                                  ((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_293 D R S_cls E),
                                    (nb095_alpha_dummy_294 u S_cls f E)),
                                  ((nb095_alpha_dummy_291 D R S_cls E),
                                    (nb095_alpha_dummy_292 u S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.ex (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                            (nb095_alpha_dummy_353 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_353;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                            (nb095_alpha_dummy_355 u S_cls) from (by
                            unfold nb095_alpha_dummy_355;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                              (nb095_alpha_dummy_354 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_354;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E)
                                      1)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                              (nb095_alpha_dummy_356 u S_cls) from (by
                              unfold nb095_alpha_dummy_356;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0359 u S_cls)
                                      1)))) (TAlphaVar.there (show
                              (nb095_alpha_dummy_346 D R S_cls E) ≠
                                (nb095_alpha_dummy_379 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_379;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0388 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_380 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_380;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0389 u S_cls)
                                        0)))) (TAlphaVar.there (show
                                (nb095_alpha_dummy_346 D R S_cls E) ≠
                                  (nb095_alpha_dummy_377 D R S_cls E) from (by
                                  unfold nb095_alpha_dummy_377;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar
                                          (nb095_support_mem_0386 D R S_cls E) 0)))) (show
                                (nb095_alpha_dummy_348 u S_cls) ≠
                                  (nb095_alpha_dummy_378 u S_cls) from (by
                                  unfold nb095_alpha_dummy_378;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb095_support_mem_0387 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                    (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                        (freshVar_injective
                          (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv) (by decide))
                        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                          (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_360 D R S_cls E) from (by
          unfold nb095_alpha_dummy_360;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls E)
                  1)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_363 u S_cls)
        from (by
          unfold nb095_alpha_dummy_363;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  1)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_359 D R S_cls E) from (by
          unfold nb095_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_362 u S_cls)
        from (by
          unfold nb095_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R
                    S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_379 D R S_cls E), (nb095_alpha_dummy_380 u S_cls)),
        ((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c1c) (by simp only [fv_syn_c1c])))
                                        (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0366
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0367
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0364
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0365
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_367;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0370
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_368 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_368;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0371
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_365 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_365;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0368
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_366 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_366;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0369
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb095_alpha_dummy_361 D R S_cls E), (nb095_alpha_dummy_364 u S_cls)),
        ((nb095_alpha_dummy_360 D R S_cls E), (nb095_alpha_dummy_363 u S_cls)),
        ((nb095_alpha_dummy_359 D R S_cls E), (nb095_alpha_dummy_362 u S_cls)),
        ((nb095_alpha_dummy_357 D R S_cls E), (nb095_alpha_dummy_358 u S_cls)),
        ((nb095_alpha_dummy_353 D R S_cls E), (nb095_alpha_dummy_355 u S_cls)),
        ((nb095_alpha_dummy_354 D R S_cls E), (nb095_alpha_dummy_356 u S_cls)),
        ((nb095_alpha_dummy_379 D R S_cls E), (nb095_alpha_dummy_380 u S_cls)),
        ((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360 D
        R S_cls E) ≠ (nb095_alpha_dummy_371 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371
        D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_371;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0374
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_372 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_372;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0375
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0372
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_363 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0373
                    u S_cls)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb095_alpha_dummy_353
        D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D
        R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D
        R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_373;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0378
                    D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_374 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_374;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0379
                    u S_cls)
                  0)))) (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_369 D R S_cls E) from (by
          unfold
            nb095_alpha_dummy_369;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0376
                    D R S_cls
                    E)
                  0)))) (show (nb095_alpha_dummy_364 u S_cls) ≠ (nb095_alpha_dummy_370 u S_cls)
        from (by
          unfold
            nb095_alpha_dummy_370;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0377
                    u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_353 D R S_cls E) ≠
                                      (nb095_alpha_dummy_357 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_355 u S_cls) ≠
                                      (nb095_alpha_dummy_358 u S_cls) from (by
                                      unfold nb095_alpha_dummy_358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                [((nb095_alpha_dummy_357 D R S_cls E),
                                    (nb095_alpha_dummy_358 u S_cls)),
                                  ((nb095_alpha_dummy_353 D R S_cls E),
                                    (nb095_alpha_dummy_355 u S_cls)),
                                  ((nb095_alpha_dummy_354 D R S_cls E),
                                    (nb095_alpha_dummy_356 u S_cls)),
                                  ((nb095_alpha_dummy_379 D R S_cls E),
                                    (nb095_alpha_dummy_380 u S_cls)),
                                  ((nb095_alpha_dummy_377 D R S_cls E),
                                    (nb095_alpha_dummy_378 u S_cls)),
                                  ((nb095_alpha_dummy_346 D R S_cls E),
                                    (nb095_alpha_dummy_348 u S_cls)),
                                  ((nb095_alpha_dummy_345 D R S_cls E),
                                    (nb095_alpha_dummy_347 u S_cls)),
                                  ((nb095_alpha_dummy_375 D R S_cls E),
                                    (nb095_alpha_dummy_376 u S_cls)),
                                  ((nb095_alpha_dummy_349 D R S_cls E),
                                    (nb095_alpha_dummy_350 u S_cls)),
                                  ((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_293 D R S_cls E),
                                    (nb095_alpha_dummy_294 u S_cls f E)),
                                  ((nb095_alpha_dummy_291 D R S_cls E),
                                    (nb095_alpha_dummy_292 u S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (show
                                  (nb095_alpha_dummy_353 D R S_cls E) ≠
                                    (nb095_alpha_dummy_357 D R S_cls E) from (by
                                    unfold nb095_alpha_dummy_357;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                  (nb095_alpha_dummy_355 u S_cls) ≠
                                    (nb095_alpha_dummy_358 u S_cls) from (by
                                    unfold nb095_alpha_dummy_358;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar
                                            (nb095_support_mem_0361 u S_cls) 0))))
                                (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb095_alpha_dummy_353 D R S_cls E) ≠
                                      (nb095_alpha_dummy_357 D R S_cls E) from (by
                                      unfold nb095_alpha_dummy_357;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                                    (nb095_alpha_dummy_355 u S_cls) ≠
                                      (nb095_alpha_dummy_358 u S_cls) from (by
                                      unfold nb095_alpha_dummy_358;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar
                                              (nb095_support_mem_0361 u S_cls) 0))))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                [((nb095_alpha_dummy_357 D R S_cls E),
                                    (nb095_alpha_dummy_358 u S_cls)),
                                  ((nb095_alpha_dummy_353 D R S_cls E),
                                    (nb095_alpha_dummy_355 u S_cls)),
                                  ((nb095_alpha_dummy_354 D R S_cls E),
                                    (nb095_alpha_dummy_356 u S_cls)),
                                  ((nb095_alpha_dummy_379 D R S_cls E),
                                    (nb095_alpha_dummy_380 u S_cls)),
                                  ((nb095_alpha_dummy_377 D R S_cls E),
                                    (nb095_alpha_dummy_378 u S_cls)),
                                  ((nb095_alpha_dummy_346 D R S_cls E),
                                    (nb095_alpha_dummy_348 u S_cls)),
                                  ((nb095_alpha_dummy_345 D R S_cls E),
                                    (nb095_alpha_dummy_347 u S_cls)),
                                  ((nb095_alpha_dummy_375 D R S_cls E),
                                    (nb095_alpha_dummy_376 u S_cls)),
                                  ((nb095_alpha_dummy_349 D R S_cls E),
                                    (nb095_alpha_dummy_350 u S_cls)),
                                  ((nb095_alpha_dummy_340 D R S_cls E),
                                    (nb095_alpha_dummy_342 u S_cls)),
                                  ((nb095_alpha_dummy_339 D R S_cls E),
                                    (nb095_alpha_dummy_341 u S_cls)),
                                  ((nb095_alpha_dummy_337 D R S_cls E),
                                    (nb095_alpha_dummy_338 u S_cls E)),
                                  ((nb095_alpha_dummy_335 D R S_cls E),
                                    (nb095_alpha_dummy_336 u S_cls E)),
                                  ((nb095_alpha_dummy_293 D R S_cls E),
                                    (nb095_alpha_dummy_294 u S_cls f E)),
                                  ((nb095_alpha_dummy_291 D R S_cls E),
                                    (nb095_alpha_dummy_292 u S_cls f E)),
                                  ((nb095_alpha_dummy_001 D R S_cls E), u),
                                  ((nb095_alpha_dummy_002 D R S_cls E), x),
                                  ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))

theorem nb095_focused_notmem_0029 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
          ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0988 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_340 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_340, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0029 D R S_cls E)
      (nb095_compact_fv_empty_0272 D R S_cls E))

theorem nb095_focused_notmem_0030 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0989 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_342 u S_cls) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_342, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0030 u S_cls) (nb095_compact_fv_empty_0273 u S_cls))

theorem nb095_focused_notmem_0031 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪
          ((syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0990 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_339 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_339, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0031 D R S_cls E)
      (nb095_compact_fv_empty_0274 D R S_cls E))

theorem nb095_focused_notmem_0032 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∉ S_cls.fv :=
  by
  change
    freshVar (((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv ∪ ((syn_csn (Class.cv u))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0991 (u : Var) (S_cls : Class) :
    (nb095_alpha_dummy_341 u S_cls) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_341, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0032 u S_cls) (nb095_compact_fv_empty_0275 u S_cls))

theorem nb095_focused_notmem_0033 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_337 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0992 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_337 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_337, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0033 D R S_cls E)
      (nb095_compact_fv_empty_0276 D R S_cls E))

theorem nb095_focused_notmem_0034 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_338 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        ((E).fv ∪ ((syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0993 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_338 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_338, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0034 u S_cls E) (nb095_compact_fv_empty_0277 u S_cls E))

theorem nb095_focused_notmem_0035 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_335 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cnin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0994 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_335 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_335, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0035 D R S_cls E)
      (nb095_compact_fv_empty_0278 D R S_cls E))

theorem nb095_focused_notmem_0036 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_336 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cnin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0995 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_336 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_336, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0036 u S_cls E) (nb095_compact_fv_empty_0279 u S_cls E))

theorem nb095_focused_notmem_0037 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_293 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0996 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_293 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_293, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0037 D R S_cls E)
      (nb095_compact_fv_empty_0222 D R S_cls E))

theorem nb095_focused_notmem_0038 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_294 u S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_crn (Class.cv f))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0997 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_294 u S_cls f E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_294, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0038 u S_cls f E)
      (nb095_compact_fv_empty_0223 u S_cls f E))

theorem nb095_focused_notmem_0039 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_291 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv ∪
          ((syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_crn (Class.cv (nb095_alpha_dummy_000 D R S_cls E)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
          (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
        (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0998 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_291 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_291, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0039 D R S_cls E)
      (nb095_compact_fv_empty_0224 D R S_cls E))

theorem nb095_focused_notmem_0040 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_292 u S_cls f E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv ∪
          ((syn_cnin (syn_crn (Class.cv f)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_crn (Class.cv f))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin E
      (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif S_cls (syn_cid))]
  rw [fv_syn_cdif S_cls (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb095_wpp_notmem_0999 (u : Var) (S_cls : Class) (f : Var) (E : Class) :
    (nb095_alpha_dummy_292 u S_cls f E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_292, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0040 u S_cls f E)
      (nb095_compact_fv_empty_0225 u S_cls f E))

theorem nb095_focused_notmem_0041 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0041 D R S_cls E)
      (nb095_compact_fv_empty_0030 D R S_cls E))

theorem nb095_wpp_notmem_1001 (u : Var) (S_cls : Class) (dv_S_u : u ∉ S_cls.fv) :
    u ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_u (nb095_compact_fv_empty_0031 u))

theorem nb095_focused_notmem_0042 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0042 D R S_cls E)
      (nb095_compact_fv_empty_0032 D R S_cls E))

theorem nb095_wpp_notmem_1003 (x : Var) (S_cls : Class) (dv_S_x : x ∉ S_cls.fv) :
    x ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_x (nb095_compact_fv_empty_0033 x))

theorem nb095_focused_notmem_0043 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ S_cls.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb095_wpp_notmem_1004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0043 D R S_cls E)
      (nb095_compact_fv_empty_0034 D R S_cls E))

theorem nb095_wpp_notmem_1005 (S_cls : Class) (f : Var) (dv_S_f : f ∉ S_cls.fv) :
    f ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_S_f (nb095_compact_fv_empty_0035 f))

theorem nb095_compact_envfresh_0120 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_293 D R S_cls E), (nb095_alpha_dummy_294 u S_cls f E)),
        ((nb095_alpha_dummy_291 D R S_cls E), (nb095_alpha_dummy_292 u S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_340 D R S_cls E)
      (nb095_alpha_dummy_342 u S_cls) (nb095_wpp_notmem_0988 D R S_cls E)
      (nb095_wpp_notmem_0989 u S_cls) (TEnvFresh.consFresh (nb095_alpha_dummy_339 D R S_cls E)
        (nb095_alpha_dummy_341 u S_cls) (nb095_wpp_notmem_0990 D R S_cls E)
        (nb095_wpp_notmem_0991 u S_cls) (TEnvFresh.consFresh (nb095_alpha_dummy_337 D R S_cls E)
          (nb095_alpha_dummy_338 u S_cls E) (nb095_wpp_notmem_0992 D R S_cls E)
          (nb095_wpp_notmem_0993 u S_cls E)
          (TEnvFresh.consFresh (nb095_alpha_dummy_335 D R S_cls E)
            (nb095_alpha_dummy_336 u S_cls E) (nb095_wpp_notmem_0994 D R S_cls E)
            (nb095_wpp_notmem_0995 u S_cls E)
            (TEnvFresh.consFresh (nb095_alpha_dummy_293 D R S_cls E)
              (nb095_alpha_dummy_294 u S_cls f E) (nb095_wpp_notmem_0996 D R S_cls E)
              (nb095_wpp_notmem_0997 u S_cls f E)
              (TEnvFresh.consFresh (nb095_alpha_dummy_291 D R S_cls E)
                (nb095_alpha_dummy_292 u S_cls f E) (nb095_wpp_notmem_0998 D R S_cls E)
                (nb095_wpp_notmem_0999 u S_cls f E)
                (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
                  (nb095_wpp_notmem_1000 D R S_cls E) (nb095_wpp_notmem_1001 u S_cls dv_S_u)
                  (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                    (nb095_wpp_notmem_1002 D R S_cls E) (nb095_wpp_notmem_1003 x S_cls dv_S_x)
                    (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                      (nb095_wpp_notmem_1004 D R S_cls E) (nb095_wpp_notmem_1005 S_cls f dv_S_f)
                      (TEnvFresh.nil ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
