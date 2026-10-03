/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C095M3Part044Stage1


/-! NF weak partition development: NAR4H5C095M3Part044. -/


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
noncomputable def nb095_focused_refl_0010 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TReflOn
      [((nb095_alpha_dummy_337 D R S_cls E), (nb095_alpha_dummy_338 u S_cls E)),
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
      E.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0336 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)

@[expose]
noncomputable def nb095_split_alpha_0098 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) :
    TAlphaWff
      [((nb095_alpha_dummy_351 D R S_cls E), (nb095_alpha_dummy_352 u S_cls)),
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
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
        ((nb095_alpha_dummy_794 D R S_cls E), (nb095_alpha_dummy_796 u S_cls E)),
        ((nb095_alpha_dummy_793 D R S_cls E), (nb095_alpha_dummy_795 u S_cls E)),
        ((nb095_alpha_dummy_797 D R S_cls E), (nb095_alpha_dummy_798 u S_cls E)),
        ((nb095_alpha_dummy_791 D R S_cls E), (nb095_alpha_dummy_792 u S_cls E)),
        ((nb095_alpha_dummy_789 D R S_cls E), (nb095_alpha_dummy_790 u S_cls E)),
        ((nb095_alpha_dummy_004 D R S_cls E), (nb095_alpha_dummy_006 x u D R S_cls f E)),
        ((nb095_alpha_dummy_003 D R S_cls E), (nb095_alpha_dummy_005 x u D R S_cls f E)),
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
                                      ((nb095_alpha_dummy_000 D R S_cls E), f)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
