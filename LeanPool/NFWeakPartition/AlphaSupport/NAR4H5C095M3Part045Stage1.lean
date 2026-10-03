/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part044

/-! NF weak partition development: NAR4H5C095M3Part045. -/


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
noncomputable def nb095_split_alpha_0099 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_379 D R S_cls E), (nb095_alpha_dummy_380 u S_cls)),
        ((nb095_alpha_dummy_377 D R S_cls E), (nb095_alpha_dummy_378 u S_cls)),
        ((nb095_alpha_dummy_346 D R S_cls E), (nb095_alpha_dummy_348 u S_cls)),
        ((nb095_alpha_dummy_345 D R S_cls E), (nb095_alpha_dummy_347 u S_cls)),
        ((nb095_alpha_dummy_375 D R S_cls E), (nb095_alpha_dummy_376 u S_cls)),
        ((nb095_alpha_dummy_349 D R S_cls E), (nb095_alpha_dummy_350 u S_cls)),
        ((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_379 D R S_cls E))
          (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_379 D R S_cls E))
            (syn_cphi (Class.cv (nb095_alpha_dummy_346 D R S_cls E))))))
      (Wff.imp (Wff.classMem (Class.cv (nb095_alpha_dummy_380 u S_cls))
          (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))) (Wff.neg
          (Wff.classMem (Class.cv (nb095_alpha_dummy_380 u S_cls))
            (syn_cphi (Class.cv (nb095_alpha_dummy_348 u S_cls)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                      (nb095_alpha_dummy_353 D R S_cls E) from (by
                      unfold nb095_alpha_dummy_353;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E) 0))))
                  (show (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_355 u S_cls) from
                    (by
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
                              (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E) 1)))) (show
                      (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_356 u S_cls) from (by
                        unfold nb095_alpha_dummy_356;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 1))))
                    (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                          (nb095_alpha_dummy_379 D R S_cls E) from (by
                          unfold nb095_alpha_dummy_379;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0388 D R S_cls E)
                                  0)))) (show
                        (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_380 u S_cls) from
                        (by
                          unfold nb095_alpha_dummy_380;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0389 u S_cls) 0))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                            (nb095_alpha_dummy_377 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_377;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0386 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                            (nb095_alpha_dummy_378 u S_cls) from (by
                            unfold nb095_alpha_dummy_378;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0387 u S_cls) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb095_alpha_dummy_353 D R S_cls E) ≠
                                        (nb095_alpha_dummy_360 D R S_cls E) from (by
                                        unfold nb095_alpha_dummy_360;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0362 D R S_cls E) 1)))) (show
                                      (nb095_alpha_dummy_355 u S_cls) ≠
                                        (nb095_alpha_dummy_363 u S_cls) from (by
                                        unfold nb095_alpha_dummy_363;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb095_support_mem_0363 u S_cls) 1))))
                                    (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_359 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_359;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0362 D R S_cls E)
                                                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠
        (nb095_alpha_dummy_362 u S_cls) from (by
                                          unfold nb095_alpha_dummy_362;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0363 u S_cls) 0))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls) 0)))) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed
                                      [((nb095_alpha_dummy_361 D R S_cls E),
        (nb095_alpha_dummy_364 u S_cls)), ((nb095_alpha_dummy_360 D R S_cls E),
        (nb095_alpha_dummy_363 u S_cls)), ((nb095_alpha_dummy_359 D R S_cls E),
        (nb095_alpha_dummy_362 u S_cls)), ((nb095_alpha_dummy_357 D R S_cls E),
        (nb095_alpha_dummy_358 u S_cls)), ((nb095_alpha_dummy_353 D R S_cls E),
        (nb095_alpha_dummy_355 u S_cls)), ((nb095_alpha_dummy_354 D R S_cls E),
        (nb095_alpha_dummy_356 u S_cls)), ((nb095_alpha_dummy_379 D R S_cls E),
        (nb095_alpha_dummy_380 u S_cls)), ((nb095_alpha_dummy_377 D R S_cls E),
        (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
                                        ((nb095_alpha_dummy_002 D R S_cls E), x),
                                        ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_367 D R S_cls E) from (by
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
                    D R S_cls E)
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠
        (nb095_alpha_dummy_367 D R S_cls E) from (by
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
                    D R S_cls E)
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
                                        [((nb095_alpha_dummy_361 D R S_cls E),
        (nb095_alpha_dummy_364 u S_cls)), ((nb095_alpha_dummy_360 D R S_cls E),
        (nb095_alpha_dummy_363 u S_cls)), ((nb095_alpha_dummy_359 D R S_cls E),
        (nb095_alpha_dummy_362 u S_cls)), ((nb095_alpha_dummy_357 D R S_cls E),
        (nb095_alpha_dummy_358 u S_cls)), ((nb095_alpha_dummy_353 D R S_cls E),
        (nb095_alpha_dummy_355 u S_cls)), ((nb095_alpha_dummy_354 D R S_cls E),
        (nb095_alpha_dummy_356 u S_cls)), ((nb095_alpha_dummy_379 D R S_cls E),
        (nb095_alpha_dummy_380 u S_cls)), ((nb095_alpha_dummy_377 D R S_cls E),
        (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_353 D R S_cls E))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠
        (nb095_alpha_dummy_371 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
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
                    D R S_cls E)
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
                              (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_358;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_357 D R S_cls E),
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
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
                              (nb095_alpha_dummy_357 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_357;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0360 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠
                              (nb095_alpha_dummy_358 u S_cls) from (by
                              unfold nb095_alpha_dummy_358;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                      0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                              (nb095_alpha_dummy_353 D R S_cls E) ≠
                                (nb095_alpha_dummy_357 D R S_cls E) from (by
                                unfold nb095_alpha_dummy_357;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar
                                        (nb095_support_mem_0360 D R S_cls E) 0)))) (show
                              (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_358;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                        0)))) (TAlphaVar.here _ _ _)))
                        (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_357 D R S_cls E),
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
                            ((nb095_alpha_dummy_794 D R S_cls E),
                              (nb095_alpha_dummy_796 u S_cls E)),
                            ((nb095_alpha_dummy_793 D R S_cls E),
                              (nb095_alpha_dummy_795 u S_cls E)),
                            ((nb095_alpha_dummy_797 D R S_cls E),
                              (nb095_alpha_dummy_798 u S_cls E)),
                            ((nb095_alpha_dummy_791 D R S_cls E),
                              (nb095_alpha_dummy_792 u S_cls E)),
                            ((nb095_alpha_dummy_789 D R S_cls E),
                              (nb095_alpha_dummy_790 u S_cls E)),
                            ((nb095_alpha_dummy_004 D R S_cls E),
                              (nb095_alpha_dummy_006 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_003 D R S_cls E),
                              (nb095_alpha_dummy_005 x u D R S_cls f E)),
                            ((nb095_alpha_dummy_001 D R S_cls E), u),
                            ((nb095_alpha_dummy_002 D R S_cls E), x),
                            ((nb095_alpha_dummy_000 D R S_cls E), f)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                        (nb095_alpha_dummy_353 D R S_cls E) from (by
                        unfold nb095_alpha_dummy_353;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb095_support_mem_0358 D R S_cls E) 0)))) (show
                      (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_355 u S_cls) from (by
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
                                  1)))) (show
                        (nb095_alpha_dummy_348 u S_cls) ≠ (nb095_alpha_dummy_356 u S_cls) from
                        (by
                          unfold nb095_alpha_dummy_356;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb095_support_mem_0359 u S_cls) 1))))
                      (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                            (nb095_alpha_dummy_379 D R S_cls E) from (by
                            unfold nb095_alpha_dummy_379;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0388 D R S_cls E)
                                    0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                            (nb095_alpha_dummy_380 u S_cls) from (by
                            unfold nb095_alpha_dummy_380;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb095_support_mem_0389 u S_cls) 0))))
                        (TAlphaVar.there (show (nb095_alpha_dummy_346 D R S_cls E) ≠
                              (nb095_alpha_dummy_377 D R S_cls E) from (by
                              unfold nb095_alpha_dummy_377;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0386 D R S_cls E)
                                      0)))) (show (nb095_alpha_dummy_348 u S_cls) ≠
                              (nb095_alpha_dummy_378 u S_cls) from (by
                              unfold nb095_alpha_dummy_378;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb095_support_mem_0387 u S_cls)
                                      0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb095_alpha_dummy_346 D R S_cls E))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb095_alpha_dummy_348 u S_cls))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb095_alpha_dummy_353 D R S_cls E) ≠
        (nb095_alpha_dummy_360 D R S_cls E) from (by
                                          unfold nb095_alpha_dummy_360;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0362 D R S_cls E)
                                                  1)))) (show (nb095_alpha_dummy_355 u S_cls) ≠
        (nb095_alpha_dummy_363 u S_cls) from (by
                                          unfold nb095_alpha_dummy_363;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb095_support_mem_0363 u S_cls) 1))))
                                      (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_359 D R S_cls E) from (by
          unfold nb095_alpha_dummy_359;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0362 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_362 u S_cls)
        from (by
          unfold nb095_alpha_dummy_362;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0363 u S_cls) 0)))) (TAlphaVar.there (show
        (nb095_alpha_dummy_353 D R S_cls E) ≠ (nb095_alpha_dummy_357 D R S_cls E) from (by
          unfold nb095_alpha_dummy_357;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0360 D R S_cls E)
                  0)))) (show (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
        from (by
          unfold nb095_alpha_dummy_358;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb095_support_mem_0361 u S_cls)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed
                                        [((nb095_alpha_dummy_361 D R S_cls E),
        (nb095_alpha_dummy_364 u S_cls)), ((nb095_alpha_dummy_360 D R S_cls E),
        (nb095_alpha_dummy_363 u S_cls)), ((nb095_alpha_dummy_359 D R S_cls E),
        (nb095_alpha_dummy_362 u S_cls)), ((nb095_alpha_dummy_357 D R S_cls E),
        (nb095_alpha_dummy_358 u S_cls)), ((nb095_alpha_dummy_353 D R S_cls E),
        (nb095_alpha_dummy_355 u S_cls)), ((nb095_alpha_dummy_354 D R S_cls E),
        (nb095_alpha_dummy_356 u S_cls)), ((nb095_alpha_dummy_379 D R S_cls E),
        (nb095_alpha_dummy_380 u S_cls)), ((nb095_alpha_dummy_377 D R S_cls E),
        (nb095_alpha_dummy_378 u S_cls)), ((nb095_alpha_dummy_346 D R S_cls E),
        (nb095_alpha_dummy_348 u S_cls)), ((nb095_alpha_dummy_345 D R S_cls E),
        (nb095_alpha_dummy_347 u S_cls)), ((nb095_alpha_dummy_375 D R S_cls E),
        (nb095_alpha_dummy_376 u S_cls)), ((nb095_alpha_dummy_349 D R S_cls E),
        (nb095_alpha_dummy_350 u S_cls)), ((nb095_alpha_dummy_340 D R S_cls E),
        (nb095_alpha_dummy_342 u S_cls)), ((nb095_alpha_dummy_339 D R S_cls E),
        (nb095_alpha_dummy_341 u S_cls)), ((nb095_alpha_dummy_337 D R S_cls E),
        (nb095_alpha_dummy_338 u S_cls E)), ((nb095_alpha_dummy_335 D R S_cls E),
        (nb095_alpha_dummy_336 u S_cls E)), ((nb095_alpha_dummy_794 D R S_cls E),
        (nb095_alpha_dummy_796 u S_cls E)), ((nb095_alpha_dummy_793 D R S_cls E),
        (nb095_alpha_dummy_795 u S_cls E)), ((nb095_alpha_dummy_797 D R S_cls E),
        (nb095_alpha_dummy_798 u S_cls E)), ((nb095_alpha_dummy_791 D R S_cls E),
        (nb095_alpha_dummy_792 u S_cls E)), ((nb095_alpha_dummy_789 D R S_cls E),
        (nb095_alpha_dummy_790 u S_cls E)), ((nb095_alpha_dummy_004 D R S_cls E),
        (nb095_alpha_dummy_006 x u D R S_cls f E)), ((nb095_alpha_dummy_003 D R S_cls E),
        (nb095_alpha_dummy_005 x u D R S_cls f E)), ((nb095_alpha_dummy_001 D R S_cls E), u),
        ((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_367 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
        ((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb095_alpha_dummy_355 u S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb095_alpha_dummy_353 D R S_cls E))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb095_alpha_dummy_355 u
        S_cls))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.there (show (nb095_alpha_dummy_360 D R S_cls E) ≠ (nb095_alpha_dummy_371 D R
        S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
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
                    D R S_cls E)
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
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb095_alpha_dummy_361 D R S_cls E) ≠ (nb095_alpha_dummy_373 D R S_cls E) from (by
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
                    D R S_cls E)
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
                                        (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_357 D R S_cls E),
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
                              ((nb095_alpha_dummy_794 D R S_cls E),
                                (nb095_alpha_dummy_796 u S_cls E)),
                              ((nb095_alpha_dummy_793 D R S_cls E),
                                (nb095_alpha_dummy_795 u S_cls E)),
                              ((nb095_alpha_dummy_797 D R S_cls E),
                                (nb095_alpha_dummy_798 u S_cls E)),
                              ((nb095_alpha_dummy_791 D R S_cls E),
                                (nb095_alpha_dummy_792 u S_cls E)),
                              ((nb095_alpha_dummy_789 D R S_cls E),
                                (nb095_alpha_dummy_790 u S_cls E)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
                              (nb095_alpha_dummy_355 u S_cls) ≠ (nb095_alpha_dummy_358 u S_cls)
                              from (by
                                unfold nb095_alpha_dummy_358;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                        0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
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
                                        (mem_lt_freshVar (nb095_support_mem_0361 u S_cls)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed [((nb095_alpha_dummy_357 D R S_cls E),
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
                              ((nb095_alpha_dummy_794 D R S_cls E),
                                (nb095_alpha_dummy_796 u S_cls E)),
                              ((nb095_alpha_dummy_793 D R S_cls E),
                                (nb095_alpha_dummy_795 u S_cls E)),
                              ((nb095_alpha_dummy_797 D R S_cls E),
                                (nb095_alpha_dummy_798 u S_cls E)),
                              ((nb095_alpha_dummy_791 D R S_cls E),
                                (nb095_alpha_dummy_792 u S_cls E)),
                              ((nb095_alpha_dummy_789 D R S_cls E),
                                (nb095_alpha_dummy_790 u S_cls E)),
                              ((nb095_alpha_dummy_004 D R S_cls E),
                                (nb095_alpha_dummy_006 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_003 D R S_cls E),
                                (nb095_alpha_dummy_005 x u D R S_cls f E)),
                              ((nb095_alpha_dummy_001 D R S_cls E), u),
                              ((nb095_alpha_dummy_002 D R S_cls E), x),
                              ((nb095_alpha_dummy_000 D R S_cls E), f)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb095_focused_notmem_0094 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
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

theorem nb095_wpp_notmem_2160 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_794, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0094 D R S_cls E)
      (nb095_compact_fv_empty_0614 D R S_cls E))

theorem nb095_focused_notmem_0095 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        1 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
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

theorem nb095_wpp_notmem_2161 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_796, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0095 u S_cls E) (nb095_compact_fv_empty_0615 u S_cls E))

theorem nb095_focused_notmem_0096 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
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

theorem nb095_wpp_notmem_2162 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_793, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0096 D R S_cls E)
      (nb095_compact_fv_empty_0616 D R S_cls E))

theorem nb095_focused_notmem_0097 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u))))).fv ∪ ((syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
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

theorem nb095_wpp_notmem_2163 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_795, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0097 u S_cls E) (nb095_compact_fv_empty_0617 u S_cls E))

theorem nb095_focused_notmem_0098 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_797 D R S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
            ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
            (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
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

theorem nb095_wpp_notmem_2164 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_797 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_797, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0098 D R S_cls E)
      (nb095_compact_fv_empty_0618 D R S_cls E))

theorem nb095_focused_notmem_0099 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_798 u S_cls E) ∉ S_cls.fv :=
  by
  change
    freshVar
        (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
            ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
              (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                  (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                    (syn_csn (Class.cv u))))))).fv)
        0 ∉
      S_cls.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
      (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
          (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E))
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

theorem nb095_wpp_notmem_2165 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_798 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_798, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0099 u S_cls E) (nb095_compact_fv_empty_0619 u S_cls E))

theorem nb095_wpp_notmem_2166 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_791 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_791, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0072 D R S_cls E)
      (nb095_compact_fv_empty_0620 D R S_cls E))

theorem nb095_wpp_notmem_2167 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_792 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_792, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0073 u S_cls E) (nb095_compact_fv_empty_0621 u S_cls E))

theorem nb095_wpp_notmem_2168 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_789 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_789, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0074 D R S_cls E)
      (nb095_compact_fv_empty_0622 D R S_cls E))

theorem nb095_wpp_notmem_2169 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_790 u S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_790, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0075 u S_cls E) (nb095_compact_fv_empty_0623 u S_cls E))

theorem nb095_wpp_notmem_2170 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0076 D R S_cls E)
      (nb095_compact_fv_empty_0436 D R S_cls E))

theorem nb095_wpp_notmem_2171 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∉
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
  by
  simpa only [nb095_alpha_dummy_006, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0077 x u D R S_cls f E)
      (nb095_compact_fv_empty_0437 x u D R S_cls f E))

theorem nb095_wpp_notmem_2172 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_003 D R S_cls E) ∉ ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv := by
  simpa only [nb095_alpha_dummy_003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0078 D R S_cls E)
      (nb095_compact_fv_empty_0434 D R S_cls E))

theorem nb095_wpp_notmem_2173 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_005 x u D R S_cls f E) ∉
      ((syn_ccnv (syn_cdif S_cls (syn_cid)))).fv :=
  by
  simpa only [nb095_alpha_dummy_005, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb095_focused_notmem_0079 x u D R S_cls f E)
      (nb095_compact_fv_empty_0435 x u D R S_cls f E))

theorem nb095_compact_envfresh_0344 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_S_f : f ∉ S_cls.fv) (dv_S_u : u ∉ S_cls.fv)
    (dv_S_x : x ∉ S_cls.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_340 D R S_cls E), (nb095_alpha_dummy_342 u S_cls)),
        ((nb095_alpha_dummy_339 D R S_cls E), (nb095_alpha_dummy_341 u S_cls)),
        ((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
        ((nb095_alpha_dummy_335 D R S_cls E), (nb095_alpha_dummy_336 u S_cls E)),
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
            (TEnvFresh.consFresh (nb095_alpha_dummy_794 D R S_cls E)
              (nb095_alpha_dummy_796 u S_cls E) (nb095_wpp_notmem_2160 D R S_cls E)
              (nb095_wpp_notmem_2161 u S_cls E)
              (TEnvFresh.consFresh (nb095_alpha_dummy_793 D R S_cls E)
                (nb095_alpha_dummy_795 u S_cls E) (nb095_wpp_notmem_2162 D R S_cls E)
                (nb095_wpp_notmem_2163 u S_cls E)
                (TEnvFresh.consFresh (nb095_alpha_dummy_797 D R S_cls E)
                  (nb095_alpha_dummy_798 u S_cls E) (nb095_wpp_notmem_2164 D R S_cls E)
                  (nb095_wpp_notmem_2165 u S_cls E)
                  (TEnvFresh.consFresh (nb095_alpha_dummy_791 D R S_cls E)
                    (nb095_alpha_dummy_792 u S_cls E) (nb095_wpp_notmem_2166 D R S_cls E)
                    (nb095_wpp_notmem_2167 u S_cls E)
                    (TEnvFresh.consFresh (nb095_alpha_dummy_789 D R S_cls E)
                      (nb095_alpha_dummy_790 u S_cls E) (nb095_wpp_notmem_2168 D R S_cls E)
                      (nb095_wpp_notmem_2169 u S_cls E)
                      (TEnvFresh.consFresh (nb095_alpha_dummy_004 D R S_cls E)
                        (nb095_alpha_dummy_006 x u D R S_cls f E)
                        (nb095_wpp_notmem_2170 D R S_cls E)
                        (nb095_wpp_notmem_2171 x u D R S_cls f E)
                        (TEnvFresh.consFresh (nb095_alpha_dummy_003 D R S_cls E)
                          (nb095_alpha_dummy_005 x u D R S_cls f E)
                          (nb095_wpp_notmem_2172 D R S_cls E)
                          (nb095_wpp_notmem_2173 x u D R S_cls f E)
                          (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
                            (nb095_wpp_notmem_1000 D R S_cls E)
                            (nb095_wpp_notmem_1001 u S_cls dv_S_u)
                            (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
                              (nb095_wpp_notmem_1002 D R S_cls E)
                              (nb095_wpp_notmem_1003 x S_cls dv_S_x)
                              (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
                                (nb095_wpp_notmem_1004 D R S_cls E)
                                (nb095_wpp_notmem_1005 S_cls f dv_S_f) (TEnvFresh.nil ((syn_ccnv
                                      (syn_cdif S_cls (syn_cid)))).fv)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
